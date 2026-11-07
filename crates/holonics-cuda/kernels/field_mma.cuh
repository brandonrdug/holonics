// [definition; agent-inferred, November 7] **Integer products on the tensor cores, by limbs** (Brandon, November 7, 05:59:
// "precision is a declared bit width per term … a hardware surface is just widths"). A word `v` of a declared carrier is the
// exact series of its 8-bit limbs, `v = Σ_(α<L) v_α 2^(8α)`, every limb below the top unsigned (`v_α ∈ [0, 256)`) and the
// top one signed (`v_(L−1) ∈ [−128, 128)`), so `L` limbs carry exactly the words of `[−2^(8L−1), 2^(8L−1))`; `L` is read
// from the operands' own bound, never fixed by hand (`limbs_of`). A product of two such words is the series of its limb
// products at the shifts `8(α + β)`, `Σ_k x_k y_k = Σ_s 2^(8s) Σ_(α+β=s) Σ_k x_(k,α) y_(k,β)`, and each inner sum is one
// `mma.sync … .s32.{u8,s8}.{u8,s8}.s32` of the card's tensor cores, which multiply 8-bit limbs and accumulate exactly in 32
// bits. Integer addition is associative, so the limb sums recombined by their shifts are the scalar sum's integer, the same
// bits in any order.
//
// **The accumulator's bound.** A limb product is at most `255 · 255 = 65 025` in magnitude (`u8 · u8`; `u8 · s8` is at most
// `255 · 128`, `s8 · s8` at most `128 · 128`). One accumulator per shift `s` takes, from each product entering it, at most
// `min(Lx, Ly)` limb pairs over that product's `K` terms, so `|acc_s| ≤ Σ min(Lx, Ly) · K · 65 025`; each caller states that
// its sum stays below `2^31` (one product of two 4-limb words keeps it for `K ≤ 8 256`), and its recombination by shift
// (`tile_combine`) is exact on 128 bits.
//
// Included by `field.cu` after the helpers it reads.

// The limbs a word of magnitude at most `m` takes, its top limb signed: the least `L` with `m < 2^(8L − 1)`, at most
// `most` (the carrier's own limbs, which also hold its one word `−2^(8·most − 1)` of magnitude `2^(8·most − 1)`).
__device__ __forceinline__ uint32_t limbs_of(uint64_t m, uint32_t most) {
    const uint32_t bits = m == 0 ? 0 : 64 - __clzll(m);
    const uint32_t l = (bits + 8) / 8;
    return l < 1 ? 1 : (l > most ? most : l);
}

// Limb `alpha` of four words (bits `8α … 8α + 7` of each), packed into one 32-bit register in their order: the register an
// `mma` operand fragment holds for four consecutive `k`. A signed top limb is its two's complement byte.
__device__ __forceinline__ uint32_t limb_pack(int64_t a, int64_t b, int64_t c, int64_t d, uint32_t alpha) {
    const uint32_t s = 8 * alpha;
    return ((uint32_t)((uint64_t)a >> s) & 0xFFu) | (((uint32_t)((uint64_t)b >> s) & 0xFFu) << 8) | (((uint32_t)((uint64_t)c >> s) & 0xFFu) << 16) | (((uint32_t)((uint64_t)d >> s) & 0xFFu) << 24);
}

// `d += a · b` on one `m16n8k16` tile: `a` the 16×16 limbs of the rows (two registers: row `g`, row `g + 8`, each `k = 4t …
// 4t + 3`), `b` the 16×8 limbs of the columns (one register: column `g`, `k = 4t … 4t + 3`), `g = lane / 4`, `t = lane % 4`;
// `d` rows `g` (columns `2t`, `2t + 1`) then `g + 8`.
template <bool AS, bool BS>
__device__ __forceinline__ void mma_k16(int32_t (&d)[4], uint32_t a0, uint32_t a1, uint32_t b0);

#define MMA_K16(AS, BS, AT, BT)                                                                                       \
    template <>                                                                                                       \
    __device__ __forceinline__ void mma_k16<AS, BS>(int32_t (&d)[4], uint32_t a0, uint32_t a1, uint32_t b0) {        \
        asm volatile("mma.sync.aligned.m16n8k16.row.col.s32." AT "." BT ".s32 {%0, %1, %2, %3}, {%4, %5}, {%6}, "     \
                     "{%0, %1, %2, %3};\n"                                                                            \
                     : "+r"(d[0]), "+r"(d[1]), "+r"(d[2]), "+r"(d[3])                                                 \
                     : "r"(a0), "r"(a1), "r"(b0));                                                                    \
    }
MMA_K16(false, false, "u8", "u8")
MMA_K16(false, true, "u8", "s8")
MMA_K16(true, false, "s8", "u8")
MMA_K16(true, true, "s8", "s8")

__device__ __forceinline__ void mma_k16_limbs(int32_t (&d)[4], uint32_t a0, uint32_t a1, uint32_t b0, bool as, bool bs) {
    if (as) {
        if (bs) {
            mma_k16<true, true>(d, a0, a1, b0);
        } else {
            mma_k16<true, false>(d, a0, a1, b0);
        }
    } else if (bs) {
        mma_k16<false, true>(d, a0, a1, b0);
    } else {
        mma_k16<false, false>(d, a0, a1, b0);
    }
}

// [definition; agent-inferred, November 7] **A warp's 16×8 tile of word products over a span of `16 KT` entries**: a lane
// (`g = lane / 4`, `t = lane % 4`) holds its rows' words `ra[kt][0]` (row `g`) and `ra[kt][1]` (row `g + 8`) and its
// column's `cb[kt]` (column `g`), each at `k = 16 kt + 4t … 4t + 3`, zero past the span. The rows take `la ≤ MA` limbs and
// the columns `lb ≤ MB` (warp-uniform, read from the operands' bounds by the caller), and every limb product
// `Σ_k a_(k,α) b_(k,β)` enters the accumulator of its shift `α + β`. The loops run over the carriers' most limbs with the
// limbs past `la`, `lb` skipped, so every accumulator's index is fixed when the warp is compiled (registers, not memory).
template <int MA, int MB, int KT>
__device__ __forceinline__ void tile_accumulate(int32_t (&acc)[MA + MB - 1][4], const int64_t (&ra)[KT][2][4], const int64_t (&cb)[KT][4], uint32_t la, uint32_t lb) {
#pragma unroll
    for (int alpha = 0; alpha < MA; alpha++) {
        if ((uint32_t)alpha >= la) {
            break;
        }
        uint32_t a0[KT], a1[KT];
#pragma unroll
        for (int kt = 0; kt < KT; kt++) {
            a0[kt] = limb_pack(ra[kt][0][0], ra[kt][0][1], ra[kt][0][2], ra[kt][0][3], alpha);
            a1[kt] = limb_pack(ra[kt][1][0], ra[kt][1][1], ra[kt][1][2], ra[kt][1][3], alpha);
        }
#pragma unroll
        for (int beta = 0; beta < MB; beta++) {
            if ((uint32_t)beta >= lb) {
                break;
            }
#pragma unroll
            for (int kt = 0; kt < KT; kt++) {
                const uint32_t b0 = limb_pack(cb[kt][0], cb[kt][1], cb[kt][2], cb[kt][3], beta);
                mma_k16_limbs(acc[alpha + beta], a0[kt], a1[kt], b0, (uint32_t)alpha + 1 == la, (uint32_t)beta + 1 == lb);
            }
        }
    }
}

// The tile's products recombined by their shifts, `Σ_s acc_s 2^(8s)`, exact on 128 bits (each `|acc_s| < 2^31`): the lane's
// four entries, rows `g` (columns `2t`, `2t + 1`) then `g + 8`.
template <int NS>
__device__ __forceinline__ void tile_combine(const int32_t (&acc)[NS][4], wide (&out)[4]) {
#pragma unroll
    for (int q = 0; q < 4; q++) {
        wide v = 0;
#pragma unroll
        for (int s = NS - 1; s >= 0; s--) {
            v = v * 256 + (wide)acc[s][q];
        }
        out[q] = v;
    }
}

// The warp's largest magnitude of a lane's words (the limbs' bound read from the operands themselves).
template <int KT, int R>
__device__ __forceinline__ uint64_t words_bound(const int64_t (&v)[KT][R][4]) {
    uint64_t m = 0;
#pragma unroll
    for (int kt = 0; kt < KT; kt++) {
#pragma unroll
        for (int r = 0; r < R; r++) {
#pragma unroll
            for (int k = 0; k < 4; k++) {
                const uint64_t x = mag64(v[kt][r][k]);
                m = x > m ? x : m;
            }
        }
    }
    return warp_max_u64(m);
}

template <int KT>
__device__ __forceinline__ uint64_t words_bound(const int64_t (&v)[KT][4]) {
    uint64_t m = 0;
#pragma unroll
    for (int kt = 0; kt < KT; kt++) {
#pragma unroll
        for (int k = 0; k < 4; k++) {
            const uint64_t x = mag64(v[kt][k]);
            m = x > m ? x : m;
        }
    }
    return warp_max_u64(m);
}
