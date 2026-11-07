// The energy field's card realization (`holonics::hnn::tower::field::energy`, the unified-theory reading of November 6,
// 22:52): **the faces are one stored energy's forces**, read on the card bit for bit the host's `Field::energy_pass`.
//
// [definition; agent-inferred, November 6] The energy of a region's state `x` and letters `u`, on one support (the host's
// module doc): each receiver's lock partition `−log₂ Σ_j μ_j 2^(z_ij)` a head (`field_energy_rows_l*`, its mass the exact
// series the contact sums, its logarithm read from the mass's leading bits as `log2_big` reads them), the strand pair's
// `−Re⟨c, a_t · b_(s(t))⟩` (`field_energy_pair_phi`) and each letter's rows against the sites they reach
// (`field_energy_letters_phi`), each summed per region as exact integers (any order, the same bits). The force on each
// site's chart read `−∂Φ/∂r̂`: the locks' shares as their scores' covector (`field_energy_rows_back` with the reverse's
// columns and spread), the pair's and the letters' (held: `field_energy_letter_force`). The tick's step
// (`field_energy_step`) and its certification are the host loop's (`CardField::energy_run`), which reads each region's
// energy back. The face at an open site is the energy's total derivative on its letter (the unified-theory reading of
// November 7, 00:02): its partial at the last state with the reverse's letters' covectors through the ticks and the
// opening (`field_energy_dm`, `field_energy_face` after the encoding's tied face; the reverse's kernels below).
//
// Included by `field.cu` after every helper it reads.

// The energy's grain (`ENERGY_BITS`): `Φ` on `2^(−32)` bits, each lock row's logarithm to `2^(−32)`.
#define ENERGY_BITS 32
// A row's term `face · μ · 2^(a − 123)` (`log_row`): the face and the multiplier each on `2^(−62)`, the face's fraction
// `2^(f − 1)`, so the mass `Σ face μ 2^(a − a₀)` stands at `2^(a₀ − 123)`.
#define TERM_EXPONENT 123

// A region's energy sums (`[r][ENERGY_SUMS]`, 128 bits each): the locks', the letters' and the pair's (the pair's on
// `2^(−40)`, the others on `2^(−32)`), the logarithms read, the site pairs met, whether a step moved the region, and `Φ`.
#define ENERGY_SUMS 8
#define ENERGY_LOCK 0
#define ENERGY_LETTERS 1
#define ENERGY_PAIR 2
#define ENERGY_LOGS 3
#define ENERGY_PAIRS 4
#define ENERGY_MOVED 5
#define ENERGY_PHI 6

// The block's ring sum (`Z/2^128`), held by its first thread; every thread of the block calls it.
__device__ __forceinline__ wide energy_block_sum(wide v, wide *scratch) {
    v = warp_sum(v);
    const uint32_t lane = threadIdx.x & 31, warp = threadIdx.x >> 5;
    __syncthreads();
    if (lane == 0) {
        scratch[warp] = v;
    }
    __syncthreads();
    wide total = 0;
    if (threadIdx.x == 0) {
        for (uint32_t k = 0; k < blockDim.x / 32; k++) {
            total += scratch[k];
        }
    }
    return total;
}

// [definition; agent-inferred, November 6] **A lock row's `log₂ Z` on `2^(−32)` bits** (the host's `log_row` and
// `log2_big`): the mass's binary length and its leading 63 bits (the bits `log2_reading_at` reads, whatever the mass's
// width), the mantissa's binary digits by squaring released at `2^(−62)`, and the mass's exponent `a₀ − 123`.
template <int L>
__device__ __forceinline__ wide energy_log2(const Big<L> &M, int64_t a0) {
    const uint32_t width = big_bits(M);
    uint64_t mantissa;
    if (width > 63) {
        const uint32_t shift = width - 63, q = shift >> 6, b = shift & 63;
        uint64_t lo = 0, hi = 0;
#pragma unroll
        for (int k = 0; k < L; k++) {
            lo = (uint32_t)k == q ? M.v[k] : lo;
            hi = (uint32_t)k == q + 1 ? M.v[k] : hi;
        }
        mantissa = b == 0 ? lo : (lo >> b) | (hi << (64 - b));
    } else {
        mantissa = M.v[0] << (63 - width);
    }
    uwide m = (uwide)mantissa;
    wide fraction = 0;
    for (uint32_t d = 0; d < ENERGY_BITS; d++) {
        m = (m * m) >> 62;
        fraction <<= 1;
        if (m >= ((uwide)1 << 63)) {
            fraction |= 1;
            m >>= 1;
        }
    }
    return ((wide)(width - 1) << ENERGY_BITS) + fraction + ((wide)(a0 - TERM_EXPONENT) << ENERGY_BITS);
}

// [definition; agent-inferred, November 6] **Each receiver's lock partition over the held supports** (the host's
// `energy_cell`), one warp a head and a receiving site, the carrier `L` limbs the exposure chose: the terms the exposure
// scored (a support entry's at the region block's dense address, a crowd's at its count), summed whole into the row's mass
// as the contact sums it; the row's `log₂ Z` into `rowlog[h][t]` and its negative into the region's locks' sum, one
// logarithm counted; each term's share of the mass on `2^(−63)` over its score (a crowd's at `ce[h][t][slot]`); the
// site pairs met counted (the region's, and the card's over every read). A row with no term reads no logarithm and forms
// no share.
template <int L>
__device__ void energy_rows_body(const FieldWords &w, wide *rowlog, wide *esum) {
    __shared__ RowCls rcs[CONTACT_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span, classes = w.nclasses;
    const uint64_t rows = (uint64_t)w.H * w.T;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        if (skipped_row(w, g)) {
            if (lane == 0) {
                rowlog[hg] = 0;
            }
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const int64_t *wi = w.pq + ((uint64_t)h * w.T + g) * S;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = rcs[warp].open ? 0 : crowd_slots(sites);
        const wide temper = temper_of(w, h, rcs[warp].open != 0);
        const int64_t amin = w.amin[hg];
        uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        Big<L> M = big_zero<L>();
        uint64_t met = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
            if (j == UINT32_MAX) {
                continue;
            }
            int64_t a;
            uint64_t face;
            term_of(w, (int64_t)erow[j], &a, &face);
            const int64_t sh = a - amin;
            uint32_t s = 0;
            if (sh >= (int64_t)(64 * L)) {
                atomicOr(w.status, REFUSED_CARRIER);
            } else {
                s = (uint32_t)sh;
            }
            big_add(M, big_shl(big_of<L>(coef_of(face, (uwide)1 << WEIGHT_BITS)), s));
            met += 1;
        }
        uint32_t lo = 0, hi_ = 0, lv = 0;
        uint64_t count = 0;
        if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
            count = scp[hi_ + 1] - scp[lo];
        }
        int64_t ca = 0;
        uint64_t cface = 0;
        if (count != 0) {
            term_of(w, crowd_score(w, h, wi, swp + (uint64_t)lo * S, swp + (uint64_t)(hi_ + 1) * S, count, lv, temper, g, lo > i), &ca, &cface);
            const int64_t sh = ca - amin;
            uint32_t s = 0;
            if (sh >= (int64_t)(64 * L)) {
                atomicOr(w.status, REFUSED_CARRIER);
            } else {
                s = (uint32_t)sh;
            }
            big_add(M, big_shl(big_of<L>(coef_of(cface, (uwide)count << WEIGHT_BITS)), s));
        }
        for (int o = 16; o > 0; o >>= 1) {
            const Big<L> om = shfl_big(M, o);
            big_add(M, om);
        }
        met = warp_sum_u64(met);
        const uint32_t mbits = big_bits(M);
        if (lane == 0) {
            atomicAdd(w.met, (unsigned long long)met);
            add_wide(esum + (uint64_t)ENERGY_SUMS * r + ENERGY_PAIRS, (wide)met);
            if (mbits != 0) {
                const wide log = energy_log2<L>(M, amin);
                rowlog[hg] = log;
                add_wide(esum + (uint64_t)ENERGY_SUMS * r + ENERGY_LOCK, -log);
                add_wide(esum + (uint64_t)ENERGY_SUMS * r + ENERGY_LOGS, 1);
            } else {
                rowlog[hg] = 0;
            }
        }
        if (mbits == 0) {
            if (lane < nslots) {
                w.ce[hg * w.slots + lane] = 0;
            }
            __syncwarp();
            continue;
        }
        // Each term's share of the row's mass, once, a lane a term (the contact's pass three).
        const RowDiv<L> rd = rowdiv_of(M);
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
            if (j == UINT32_MAX) {
                continue;
            }
            int64_t a;
            uint64_t face;
            term_of(w, (int64_t)erow[j], &a, &face);
            const Big<L> x = big_shl(big_of<L>(coef_of(face, (uwide)1 << WEIGHT_BITS)), (uint32_t)(a - amin) + SHARE_BITS);
            uint64_t p = 0;
            if (!rowdiv_nearest(x, rd, &p)) {
                p = UINT64_MAX;
            }
            erow[j] = p;
        }
        if (lane < nslots) {
            uint64_t p = 0;
            if (count != 0) {
                const Big<L> x = big_shl(big_of<L>(coef_of(cface, (uwide)count << WEIGHT_BITS)), (uint32_t)(ca - amin) + SHARE_BITS);
                if (!rowdiv_nearest(x, rd, &p)) {
                    p = UINT64_MAX;
                }
            }
            w.ce[hg * w.slots + lane] = p;
        }
        __syncwarp();
    }
}

#define ENERGY_ROWS_ENTRY(LL) \
    extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32, CONTACT_MIN_BLOCKS) field_energy_rows_l##LL(FieldWords w, wide *rowlog, wide *esum) { energy_rows_body<LL>(w, rowlog, esum); }
ENERGY_ROWS_ENTRY(5)
ENERGY_ROWS_ENTRY(6)
ENERGY_ROWS_ENTRY(7)
ENERGY_ROWS_ENTRY(8)
ENERGY_ROWS_ENTRY(9)
ENERGY_ROWS_ENTRY(10)
ENERGY_ROWS_ENTRY(11)
ENERGY_ROWS_ENTRY(12)
ENERGY_ROWS_ENTRY(13)
ENERGY_ROWS_ENTRY(14)
ENERGY_ROWS_ENTRY(15)
ENERGY_ROWS_ENTRY(16)
ENERGY_ROWS_ENTRY(17)
ENERGY_ROWS_ENTRY(18)
ENERGY_ROWS_ENTRY(19)
ENERGY_ROWS_ENTRY(20)

// [definition; agent-inferred, November 6] **Each site's letter in the energy** (the host's `energy_letters`): its rows of
// the encoding and of its two strand contacts (its class's, its carried face's mixture, or the unresolved row, as the
// opening reads them, `opening_term`) on `2^(−16)`, and its class bias (a carried face's mixture `release(Σ_a w_a c_a, 16)`,
// zero at an unresolved site carrying none). Held through the ticks.
extern "C" __global__ void field_energy_letters(FieldWords w, int64_t *own, int64_t *before, int64_t *after, int64_t *bias) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        own[c] = opening_term(w, w.enc, t, i);
        before[c] = opening_term(w, w.enc_before, t, i);
        after[c] = opening_term(w, w.enc_after, t, i);
        if (i == 0) {
            const uint32_t from = w.mix_off[t], to = w.mix_off[t + 1];
            int64_t b;
            if (from != to) {
                wide sum = 0;
                for (uint32_t k = from; k < to; k++) {
                    sum += (wide)w.mix_share[k] * (wide)w.theta[w.read_bias + w.mix_class[k]];
                }
                b = (int64_t)rel(sum, FACE_BITS);
            } else {
                b = w.unresolved[t] ? 0 : (int64_t)w.theta[w.read_bias + w.classes[t]];
            }
            bias[t] = b;
        }
    }
}

// [definition; agent-inferred, November 6] **The letters' force, held** (the host's `energy_force`, its last part): at fixed
// letters it does not move with the state, `release(Rᵀ E(u_t), 16) + (C s_t + b) 2^8 + E₋(u_(t−1)) 2^8 + E₊(u_(t+1)) 2^8` on
// `2^(−24)`, the strand neighbours within the site's region.
extern "C" __global__ void field_energy_letter_force(FieldWords w, const int64_t *own, const int64_t *before, const int64_t *after, const int64_t *mterm, int64_t *lf) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    const uint32_t up = COVECTOR_BITS - FACE_BITS;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        wide sum = 0;
        for (uint32_t o = 0; o < w.D; o++) {
            sum += (wide)w.theta[w.read + (uint64_t)o * w.D + i] * (wide)own[t * w.D + o];
        }
        wide v = (wide)fit64(rel(sum, FACE_BITS), w.status) + ((wide)mterm[c] << up);
        if (w.site_pos[t] > 0) {
            v += (wide)before[(t - 1) * w.D + i] << up;
        }
        if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
            v += (wide)after[(t + 1) * w.D + i] << up;
        }
        lf[c] = fit64(v, w.status);
    }
}

// [definition; agent-inferred, November 6] **The letters' energy** of each region (the host's `energy_cell`, its last part):
// `−Σ_t [⟨E(u_t), R r̂_t + b_R⟩ + c_(u_t) 2^16 + ⟨C s_t + b, r̂_t⟩ + ⟨E₋(u_t), r̂_(t+1)⟩ + ⟨E₊(u_t), r̂_(t−1)⟩]` on `2^(−32)`, one
// block a region, its sites over the block's threads, summed as exact integers.
extern "C" __global__ void field_energy_letters_phi(FieldWords w, const int32_t *read, const int64_t *lift, const int64_t *own, const int64_t *before, const int64_t *after, const int64_t *bias, const int64_t *mterm, wide *esum) {
    __shared__ wide scratch[32];
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        wide acc = 0;
        for (uint32_t t = threadIdx.x; t < sites; t += blockDim.x) {
            const uint64_t g = first + t;
            const uint64_t at = g * w.D;
            wide s = (wide)bias[g] << FACE_BITS;
            for (uint32_t i = 0; i < w.D; i++) {
                s += (wide)own[at + i] * (wide)lift[at + i] + (wide)mterm[at + i] * (wide)read[at + i];
            }
            if (t + 1 < sites) {
                for (uint32_t i = 0; i < w.D; i++) {
                    s += (wide)before[at + i] * (wide)read[at + w.D + i];
                }
            }
            if (t > 0) {
                for (uint32_t i = 0; i < w.D; i++) {
                    s += (wide)after[at + i] * (wide)read[at - w.D + i];
                }
            }
            acc -= s;
        }
        acc = energy_block_sum(acc, scratch);
        if (threadIdx.x == 0) {
            add_wide(esum + (uint64_t)ENERGY_SUMS * r + ENERGY_LETTERS, acc);
        }
    }
}

// [definition; agent-inferred, November 6] **The strand pair's energy** of each region (the host's `energy_cell`):
// `−Σ_t Σ_(e<f/2) [c_re release(a_re b_re − a_im b_im, 16) + c_im release(a_re b_im + a_im b_re, 16)]` with `b` the strand
// mate's (§16.34), on `2^(−40)`, one block a region; the sum is released once to `2^(−32)` with the region's `Φ`.
extern "C" __global__ void field_energy_pair_phi(FieldWords w, uint64_t pair_c, wide *esum) {
    __shared__ wide scratch[32];
    const uint32_t half = w.f / 2;
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        wide acc = 0;
        for (uint64_t c = threadIdx.x; c < (uint64_t)sites * half; c += blockDim.x) {
            const uint64_t g = first + c / half, e = c % half;
            const uint64_t s = strand_mate(w, g, e);
            if (s == UINT64_MAX) {
                continue;
            }
            const wide ar = w.pa[g * w.f + e], ai = w.pa[g * w.f + half + e];
            const wide br = w.pb[s * w.f + e], bi = w.pb[s * w.f + half + e];
            const wide pr = rel(ar * br - ai * bi, FACE_BITS), pi = rel(ar * bi + ai * br, FACE_BITS);
            acc -= (wide)w.theta[pair_c + e] * pr + (wide)w.theta[pair_c + half + e] * pi;
        }
        acc = energy_block_sum(acc, scratch);
        if (threadIdx.x == 0) {
            add_wide(esum + (uint64_t)ENERGY_SUMS * r + ENERGY_PAIR, acc);
        }
    }
}

// Each region's energy `Φ = locks + letters + release(pair, 40 − 32)` on `2^(−32)` bits, one thread a region.
extern "C" __global__ void field_energy_phi(FieldWords w, wide *esum) {
    for (uint64_t r = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; r < w.R; r += (uint64_t)gridDim.x * blockDim.x) {
        wide *s = esum + ENERGY_SUMS * r;
        s[ENERGY_PHI] = s[ENERGY_LOCK] + s[ENERGY_LETTERS] + rel(s[ENERGY_PAIR], MATERIAL_BITS + FACE_BITS - ENERGY_BITS);
    }
}

// The lock force's score covector from a share (the host's `energy_force`): `release(T · release(p, 63 − 40), 24)`, the
// share read as `−∂Φ/∂z` on `2^(−40)` through the receiver's temperature.
__device__ __forceinline__ int64_t energy_ds(const FieldWords &w, wide temper, uint64_t p) {
    return fit64(rel(temper * rel((wide)p, SHARE_BITS - CONTACT_BITS), MATERIAL_BITS), w.status);
}

// [definition; agent-inferred, November 6] **The locks' force over one head's rows** (the host's `energy_force`), one warp
// a receiving site `i`: each met source's score covector `δs_ij` from its share (`energy_ds`) held at the region block's
// dense address `[i][j]` for the columns (the key role, `field_contact_columns`); the probe role `release(Σ δs D ŵ_j +
// Σ_C div_nearest(δs_C D W_C, |C|), 32 + g)` written to the probe chart's framed slot, the key chart's slot zeroed for the
// columns; a crowd's key role `δs_C (D p̃_i |C| 2^g − D² W_C) / |C|²` spread over its members by the difference array `cw`
// (`field_spread`). The training's `field_contact_rows` with the share in the comparison's place, and no values.
extern "C" __global__ void __launch_bounds__(REV_ROWS * 32, 6) field_energy_rows_back(FieldWords w, uint32_t h, int64_t *ds, int64_t *dq) {
    __shared__ uint32_t stj[REV_ROWS][32];
    __shared__ int64_t dss[REV_ROWS][32];
    __shared__ int64_t dsks[REV_ROWS][MAX_CROWD_SLOTS];
    __shared__ uint64_t cnts[REV_ROWS][32];
    __shared__ uint32_t crlo[REV_ROWS][32], crhi[REV_ROWS][32], crlv[REV_ROWS][32];
    __shared__ Divisor cdiv[REV_ROWS][32], cdiv2[REV_ROWS][32];
    __shared__ RowCls rcs[REV_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n, classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const bool active = lane < S * parts;
    const uint32_t entry = lane % S, part = lane / S, m = entry % n;
    const bool still = skinless(w, h);
    const uint32_t g0 = still ? 0 : MOVE_BITS;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint64_t hg = (uint64_t)h * w.T + g;
        if (skipped_row(w, g)) {
            if (lane < S) {
                const uint32_t mc = h * n + lane % n;
                const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
                w.dp[slot] = 0;
                dq[slot] = 0;
            }
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint32_t i = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        int64_t *dsr = ds + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = rcs[warp].open ? 0 : crowd_slots(sites);
        const wide temper = temper_of(w, h, rcs[warp].open != 0);
        {
            uint64_t count = 0;
            uint32_t lo = 0, hi_ = 0, lv = 0;
            if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                count = scp[hi_ + 1] - scp[lo];
            }
            cnts[warp][lane] = count;
            crlo[warp][lane] = lo;
            crhi[warp][lane] = hi_;
            crlv[warp][lane] = lv;
            if (count != 0) {
                cdiv[warp][lane] = divisor_of(count);
                cdiv2[warp][lane] = divisor_of(count * count);
            }
        }
        __syncwarp();
        // The pairs' δs, in chunks of 32 into the warp's shared chunk, whose sum over the word is read with the lanes over
        // the span's entries (the probe role: `δs D ŵ_j`).
        wide sum = 0;
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, rcs[warp], i, sites, k) : UINT32_MAX;
            int64_t dsv = 0;
            if (j != UINT32_MAX) {
                dsv = energy_ds(w, temper, e[j]);
                dsr[j] = dsv;
            }
            dss[warp][lane] = dsv;
            stj[warp][lane] = j;
            __syncwarp();
            if (active) {
                for (uint32_t jj = part; jj < 32; jj += parts) {
                    const uint32_t jx = stj[warp][jj];
                    if (jx != UINT32_MAX) {
                        sum += (wide)dss[warp][jj] * skin_raw(w, h, m, g, first + jx, jx > i ? jx - i : i - jx) * (wide)words[(uint64_t)jx * S + entry];
                    }
                }
            }
            __syncwarp();
        }
        if (cnts[warp][lane] != 0) {
            dsks[warp][lane] = energy_ds(w, temper, w.ce[hg * w.slots + lane]);
        }
        __syncwarp();
        if (active) {
            for (uint32_t jj = part; jj < nslots; jj += parts) {
                const uint64_t count = cnts[warp][jj];
                if (count == 0) {
                    continue;
                }
                const uint32_t lo = crlo[warp][jj], hi_ = crhi[warp][jj], lv = crlv[warp][jj];
                const wide d = skin_raw(w, h, m, g, octave_edge(g, lv, lo > i), (uint32_t)1 << lv);
                const wide dsk = dsks[warp][jj];
                const wide wsum = swp[(uint64_t)(hi_ + 1) * S + entry] - swp[(uint64_t)lo * S + entry];
                sum += div_nearest_by(dsk * d * wsum, cdiv[warp][jj]);
                // The key's bracket released by the skin's bits once, its product by the covector checked.
                const wide bracket = rel(((d * (wide)w.pq[((uint64_t)h * w.T + g) * S + entry] * (wide)count) << g0) - d * d * wsum, g0);
                wide prod = 0;
                if (!mul_fits(dsk, bracket, &prod)) {
                    atomicOr(w.status, REFUSED_KEY);
                }
                const wide pw = div_nearest_by(prod, cdiv2[warp][jj]);
                add_wide(w.cw + (first + r + lo) * S + entry, pw);
                add_wide(w.cw + (first + r + hi_ + 1) * S + entry, -pw);
            }
        }
        sum = parts_sum(active ? sum : 0, S, parts);
        if (lane < S) {
            const uint32_t mc = h * n + lane % n;
            const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
            w.dp[slot] = fit64(rel(sum, CONTACT_BACK + g0), w.status);
            dq[slot] = 0;
        }
        __syncwarp();
    }
}

// The force's letters part added (`fit64`, the host's addition).
extern "C" __global__ void field_energy_force_add(FieldWords w, const int64_t *lf, int64_t *force) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        force[c] = fit64((wide)force[c] + (wide)lf[c], w.status);
    }
}

// The pair's contraction `c` at every site's contacts (`[t][f]`): the pair's force is the complex product's return
// (`field_pair_back`) of the covector `c` at each site.
extern "C" __global__ void field_energy_pair_c(FieldWords w, uint64_t pair_c, int64_t *dc) {
    const uint64_t cells = (uint64_t)w.T * w.f;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        dc[c] = w.theta[pair_c + c % w.f];
    }
}

// [definition; agent-inferred, November 6] **One descent step** (the host's `energy_step`): each site's lanes moved by
// `2^(−h)` of their own scale a unit of force, `x + release(‖x‖_rms F, 24 + h)`, `h` the region's halvings
// (`UINT32_MAX`: the region rests this round and its state is copied); whether the step moved each region is raised into
// its sums.
extern "C" __global__ void field_energy_step(FieldWords w, const int64_t *x, const wide *scale, const int64_t *force, const uint32_t *halvings, int64_t *next, wide *esum) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    const uint32_t lw = w.D / w.lanes;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        const uint32_t r = w.site_region[t];
        const uint32_t h = halvings[r];
        if (h == UINT32_MAX) {
            next[c] = x[c];
            continue;
        }
        const wide s = scale[t * w.lanes + i / lw];
        const int64_t v = fit64((wide)x[c] + rel(s * (wide)force[c], COVECTOR_BITS + h), w.status);
        next[c] = v;
        if (v != x[c]) {
            esum[(uint64_t)ENERGY_SUMS * r + ENERGY_MOVED] = 1;
        }
    }
}

// A certified step taken: the regions it certified copy the stepped state.
extern "C" __global__ void field_energy_accept(FieldWords w, const int64_t *next, int64_t *x, const uint8_t *accept) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        if (accept[w.site_region[c / w.D]]) {
            x[c] = next[c];
        }
    }
}

// The moment's covector of the face (the host's `energy_faces`): `dm = release(Cᵀ r̂_t, 16) + δp_t − m_t` (`[t][2M]`, held on
// 128 bits for the moments' return), `C` the moment's chart into the face, `δp` the probes' share of the force and `m` the
// reverse's moment covector (the opening's and the ticks', `field_energy_reverse_letters`, `field_energy_opening_letters`).
extern "C" __global__ void field_energy_dm(FieldWords w, uint64_t mface, const int32_t *read, const int64_t *dp, const int64_t *total, wide *dm) {
    const uint64_t cells = (uint64_t)w.T * w.M2;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.M2, k = c % w.M2;
        wide sum = 0;
        for (uint32_t o = 0; o < w.D; o++) {
            sum += (wide)w.theta[mface + (uint64_t)o * w.M2 + k] * (wide)read[t * w.D + o];
        }
        const int64_t back = fit64(rel(sum, FACE_BITS), w.status);
        dm[c] = fit64((wide)back + (wide)dp[c] - (wide)total[c], w.status);
    }
}

// [definition; the unified-theory reading of November 7, 00:02] **The face is the total derivative of the energy at the last
// state** (the host's `energy_faces`): at each unresolved site, onto the encoding's tied face `z(a)`, the strand rows against
// the sites they reach, `release(⟨E₋(a), r̂_(t+1)⟩ + ⟨E₊(a), r̂_(t−1)⟩, 16)`, and `release(μ − θ, 24)`: the moment's part `μ = Σ_k
// E⁻_m(a)_k δb_t[k] + E⁺_m(a)_k δa_t[k]` through the moment's return (`d_before`, `d_after`, `[u][t]` pairs on 128 bits) and the
// opening's and the ticks' part `θ = ⟨E(a), λ_own⟩ + ⟨E₋(a), λ_before⟩ + ⟨E₊(a), λ_after⟩` on the letters' covectors (`[t][D]` on
// `2^(−24)`, the reverse's).
extern "C" __global__ void field_energy_face(FieldWords w, const int32_t *read, const wide *dbefore, const wide *dafter, uint32_t tm, uint64_t mbefore, uint64_t mafter, const int64_t *own, const int64_t *before, const int64_t *after, int64_t *z) {
    const uint64_t cells = (uint64_t)w.T * w.A;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.A, a = c % w.A;
        if (!w.unresolved[t]) {
            continue;
        }
        wide strand = 0;
        if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
            for (uint32_t i = 0; i < w.D; i++) {
                strand += (wide)w.theta[w.enc_before + a * w.D + i] * (wide)read[(t + 1) * w.D + i];
            }
        }
        if (w.site_pos[t] > 0) {
            for (uint32_t i = 0; i < w.D; i++) {
                strand += (wide)w.theta[w.enc_after + a * w.D + i] * (wide)read[(t - 1) * w.D + i];
            }
        }
        wide through = 0;
        for (uint32_t i = 0; i < w.D; i++) {
            through += (wide)w.theta[w.enc + a * w.D + i] * (wide)own[t * w.D + i] + (wide)w.theta[w.enc_before + a * w.D + i] * (wide)before[t * w.D + i] + (wide)w.theta[w.enc_after + a * w.D + i] * (wide)after[t * w.D + i];
        }
        wide part = 0;
        for (uint32_t k = 0; k < 2 * tm; k++) {
            const uint32_t u = k < tm ? k : k - tm;
            const uint64_t at = (uint64_t)u * 2 * w.T + 2 * t + (k < tm ? 0 : 1);
            part += (wide)w.theta[mbefore + a * 2 * tm + k] * dbefore[at] + (wide)w.theta[mafter + a * 2 * tm + k] * dafter[at];
        }
        z[c] = fit64((wide)z[c] + rel(strand, FACE_BITS) + rel(part - through, COVECTOR_BITS), w.status);
    }
}

// -------------------------------------------------------------------------------------------
// the force's tangent and the reverse through the ticks (the unified-theory reading of November 7, 00:02)
//
// [definition; agent-inferred, November 7] **The force's tangent** `δF = −Hess Φ · v` (the host's `energy_tangent` and
// `lock_words` with a tangent), launch for launch: the words' tangents through the charts with no bias
// (`field_affine_*` at `NO_BIAS`) and the frame (`field_frame_probe`), through the unit power (`field_energy_unit_tangent`),
// their prefix sums (`field_sums`), the locks' scores', shares' and brackets' tangents beside the force on the words
// (`field_energy_tangent_rows`, `field_energy_tangent_columns`, `field_energy_spread`), the unit power's return differentiated
// (`field_energy_unit_tangent_back`), the frame's and the charts' transposes, and the pair's (`field_energy_pair_tangent`).
// **The reverse** (the host's `energy_reverse`): from `λ^K = −J F^K` back over each tick that stood at its halvings `h`,
// `w = s ⊙ λ'` (`field_energy_scaled`), the tick's letters (`field_energy_reverse_letters`), and `λ = λ' + 2^(−h) (r̂⟨λ', F⟩/W
// + J δF(w))` (`field_energy_lambda`); then the opening's (`field_energy_opening_letters`).

// A pair's score tangent on `2^(−40)` (the host's `lock_words`): `Σ_m [D (δp̂·k̂ + p̂·δk̂) 2^g − D² k̂·δk̂]`, each product
// checked as the host's, released `2g` and through the receiver's temperature.
__device__ __forceinline__ wide energy_pair_dz(const FieldWords &w, uint32_t h, const int64_t *pi, const int64_t *tpi, const int64_t *qj, const int64_t *tkj, uint64_t gi, uint64_t gj, uint32_t gap, wide temper) {
    const uint32_t g = skinless(w, h) ? 0 : MOVE_BITS;
    wide acc = 0;
    for (uint32_t l = 0; l < w.n; l++) {
        const wide dec = skin_raw(w, h, l, gi, gj, gap);
        wide pair = 0, power = 0;
        for (uint32_t r = l; r < w.span; r += w.n) {
            pair += (wide)tpi[r] * (wide)qj[r] + (wide)pi[r] * (wide)tkj[r];
            power += (wide)qj[r] * (wide)tkj[r];
        }
        wide lifted, next;
        if (!mul_fits(dec * pair, (wide)1 << g, &lifted) || !add_fits(acc, lifted - dec * dec * power, &next)) {
            atomicOr(w.status, REFUSED_KEY);
            return 0;
        }
        acc = next;
    }
    return rel(temper * rel(acc, 2 * g), MATERIAL_BITS);
}

// A crowd's score tangent on `2^(−40)` (the host's `lock_words`): its summed word `W` and its tangent `δW` over its `count`,
// `div_nearest(Σ_m [D (δp̂·W + p̂·δW) 2^g |C| − D² W·δW], |C|²)`, released `2g` and through the temperature.
__device__ __forceinline__ wide energy_crowd_dz(const FieldWords &w, uint32_t h, const int64_t *pi, const int64_t *tpi, const wide *swlo, const wide *swhi, const wide *tswlo, const wide *tswhi, uint64_t count, uint32_t level, uint64_t gi, bool right, wide temper) {
    const uint32_t g = skinless(w, h) ? 0 : MOVE_BITS;
    wide acc = 0;
    for (uint32_t l = 0; l < w.n; l++) {
        const wide dec = skin_raw(w, h, l, gi, octave_edge(gi, level, right), (uint32_t)1 << level);
        wide pair = 0, power = 0;
        for (uint32_t r = l; r < w.span; r += w.n) {
            const wide W = swhi[r] - swlo[r], dW = tswhi[r] - tswlo[r];
            pair += (wide)tpi[r] * W + (wide)pi[r] * dW;
            power += W * dW;
        }
        wide lifted, counted, next;
        if (!mul_fits(dec * pair, (wide)1 << g, &lifted) || !mul_fits(lifted, (wide)count, &counted) || !add_fits(acc, counted - dec * dec * power, &next)) {
            atomicOr(w.status, REFUSED_KEY);
            return 0;
        }
        acc = next;
    }
    return rel(temper * rel(div_nearest(acc, (wide)(count * count)), 2 * g), MATERIAL_BITS);
}

// A share's tangent on `2^(−63)` (`ln 2 · p (δz − Σ p δz)`), carried to the score covector as a share is (`energy_ds`'s law).
__device__ __forceinline__ wide energy_tds(const FieldWords &w, wide temper, uint64_t p, wide dz, wide mean) {
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    const wide dp = rel(ln2 * rel((wide)p * (dz - mean), CONTACT_BITS), MOVE_BITS);
    return rel(temper * rel(dp, SHARE_BITS - CONTACT_BITS), MATERIAL_BITS);
}

// The unit power's return (`ratio_adjoint`) of a framed word's covector over each head's span, `[h][t][2n]` both: the words'
// tangents through the unit power. One warp a head and a site.
extern "C" __global__ void field_energy_unit_tangent(FieldWords w, const int64_t *unit, const wide *scale, const int64_t *framed, int64_t *out) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        const wide s = scale[hs];
        const int64_t *u = unit + hs * w.span;
        const int64_t *f = framed + hs * w.span;
        wide dot = 0;
        for (uint32_t c = lane; c < w.span; c += 32) {
            dot += (wide)u[c] * (wide)f[c];
        }
        dot = warp_sum(dot);
        const wide mean = div_nearest(dot, (wide)w.span);
        for (uint32_t c = lane; c < w.span; c += 32) {
            out[hs * w.span + c] = s == 0 ? 0 : fit64(div_nearest(((wide)f[c] - rel(mean * (wide)u[c], 2 * FACE_BITS)) << FACE_BITS, s), w.status);
        }
    }
}

// [definition; agent-inferred, November 7] **The locks' force on the words and its tangent over one head's rows** (the host's
// `lock_words` with a tangent `(δk̂, δp̂)` = `(uq, up)`, `[h][t][2n]` on `2^(−24)`, their definite prefix sums `tsw`), one warp a
// receiving site `i`: each met source's score covector `δs` from its share and its tangent `δs'` from the share's tangent
// (two passes over the support: `Σ p δz`, then each term), held at the region block's dense address for the columns; the
// probe role `release(Σ δs D k̂_j + crowds, 32 + g)` into `w.dp` and its tangent `release(Σ (δs' D k̂_j 2^8 + δs D δk̂_j) +
// crowds, 40 + g)` into `tp`, the key slots zeroed for the columns (`dq`, `tq`); each crowd's key role and its tangent spread
// by the difference arrays `w.cw`, `tcw`.
extern "C" __global__ void __launch_bounds__(REV_ROWS * 32, 4) field_energy_tangent_rows(FieldWords w, uint32_t h, const int64_t *uq, const int64_t *up, const wide *tsw, int64_t *ds, wide *tds, int64_t *dq, int64_t *tq, int64_t *tp, wide *tcw) {
    __shared__ uint32_t stj[REV_ROWS][32];
    __shared__ int64_t dss[REV_ROWS][32];
    __shared__ wide tdss[REV_ROWS][32];
    __shared__ int64_t dsks[REV_ROWS][MAX_CROWD_SLOTS];
    __shared__ wide tdsks[REV_ROWS][MAX_CROWD_SLOTS];
    __shared__ uint64_t cnts[REV_ROWS][32];
    __shared__ uint32_t crlo[REV_ROWS][32], crhi[REV_ROWS][32], crlv[REV_ROWS][32];
    __shared__ Divisor cdiv[REV_ROWS][32], cdiv2[REV_ROWS][32];
    __shared__ RowCls rcs[REV_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n, classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const bool active = lane < S * parts;
    const uint32_t entry = lane % S, part = lane / S, m = entry % n;
    const bool still = skinless(w, h);
    const uint32_t g0 = still ? 0 : MOVE_BITS;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint64_t hg = (uint64_t)h * w.T + g;
        if (lane < S) {
            const uint32_t mc = h * n + lane % n;
            const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
            dq[slot] = 0;
            tq[slot] = 0;
            if (skipped_row(w, g)) {
                w.dp[slot] = 0;
                tp[slot] = 0;
            }
        }
        if (skipped_row(w, g)) {
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint32_t i = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        int64_t *dsr = ds + w.region_eoff[r] + (uint64_t)i * sites;
        wide *tdsr = tds + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *twords = uq + ((uint64_t)h * w.T + first) * S;
        const int64_t *pi = w.pq + hg * S;
        const int64_t *tpi = up + hg * S;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const wide *tswp = tsw + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = rcs[warp].open ? 0 : crowd_slots(sites);
        const wide temper = temper_of(w, h, rcs[warp].open != 0);
        {
            uint64_t count = 0;
            uint32_t lo = 0, hi_ = 0, lv = 0;
            if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                count = scp[hi_ + 1] - scp[lo];
            }
            cnts[warp][lane] = count;
            crlo[warp][lane] = lo;
            crhi[warp][lane] = hi_;
            crlv[warp][lane] = lv;
            if (count != 0) {
                cdiv[warp][lane] = divisor_of(count);
                cdiv2[warp][lane] = divisor_of(count * count);
            }
        }
        __syncwarp();
        // Pass one: `Σ p δz` over the row's terms, the pairs' and the crowds' (a crowd a lane).
        wide weighted = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
            if (j == UINT32_MAX) {
                continue;
            }
            weighted += (wide)e[j] * energy_pair_dz(w, h, pi, tpi, words + (uint64_t)j * S, twords + (uint64_t)j * S, g, first + j, j > i ? j - i : i - j, temper);
        }
        wide cdz = 0;
        if (cnts[warp][lane] != 0) {
            const uint32_t lo = crlo[warp][lane], hi_ = crhi[warp][lane], lv = crlv[warp][lane];
            cdz = energy_crowd_dz(w, h, pi, tpi, swp + (uint64_t)lo * S, swp + (uint64_t)(hi_ + 1) * S, tswp + (uint64_t)lo * S, tswp + (uint64_t)(hi_ + 1) * S, cnts[warp][lane], lv, g, lo > i, temper);
            weighted += (wide)w.ce[hg * w.slots + lane] * cdz;
        }
        const wide mean = rel(warp_sum(weighted), SHARE_BITS);
        // Pass two: each pair's δs and δs', in chunks of 32 staged for the probe role and its tangent over the span's entries.
        wide sum = 0, tsum = 0;
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, rcs[warp], i, sites, k) : UINT32_MAX;
            int64_t dsv = 0;
            wide tdsv = 0;
            if (j != UINT32_MAX) {
                dsv = energy_ds(w, temper, e[j]);
                const wide dz = energy_pair_dz(w, h, pi, tpi, words + (uint64_t)j * S, twords + (uint64_t)j * S, g, first + j, j > i ? j - i : i - j, temper);
                tdsv = energy_tds(w, temper, e[j], dz, mean);
                dsr[j] = dsv;
                tdsr[j] = tdsv;
            }
            dss[warp][lane] = dsv;
            tdss[warp][lane] = tdsv;
            stj[warp][lane] = j;
            __syncwarp();
            if (active) {
                for (uint32_t jj = part; jj < 32; jj += parts) {
                    const uint32_t jx = stj[warp][jj];
                    if (jx != UINT32_MAX) {
                        const wide dec = skin_raw(w, h, m, g, first + jx, jx > i ? jx - i : i - jx);
                        const wide q = (wide)words[(uint64_t)jx * S + entry], tk = (wide)twords[(uint64_t)jx * S + entry];
                        sum += (wide)dss[warp][jj] * dec * q;
                        tsum += ((tdss[warp][jj] * dec * q) << 8) + (wide)dss[warp][jj] * dec * tk;
                    }
                }
            }
            __syncwarp();
        }
        if (cnts[warp][lane] != 0) {
            const uint64_t p = w.ce[hg * w.slots + lane];
            dsks[warp][lane] = energy_ds(w, temper, p);
            tdsks[warp][lane] = energy_tds(w, temper, p, cdz, mean);
        }
        __syncwarp();
        if (active) {
            for (uint32_t jj = part; jj < nslots; jj += parts) {
                const uint64_t count = cnts[warp][jj];
                if (count == 0) {
                    continue;
                }
                const uint32_t lo = crlo[warp][jj], hi_ = crhi[warp][jj], lv = crlv[warp][jj];
                const wide d = skin_raw(w, h, m, g, octave_edge(g, lv, lo > i), (uint32_t)1 << lv);
                const wide dsk = dsks[warp][jj], tdsk = tdsks[warp][jj];
                const wide wsum = swp[(uint64_t)(hi_ + 1) * S + entry] - swp[(uint64_t)lo * S + entry];
                const wide twsum = tswp[(uint64_t)(hi_ + 1) * S + entry] - tswp[(uint64_t)lo * S + entry];
                sum += div_nearest_by(dsk * d * wsum, cdiv[warp][jj]);
                tsum += div_nearest_by(((tdsk * d * wsum) << 8) + dsk * d * twsum, cdiv[warp][jj]);
                const wide bracket = rel(((d * (wide)pi[entry] * (wide)count) << g0) - d * d * wsum, g0);
                const wide tbracket = rel(((d * (wide)tpi[entry] * (wide)count) << g0) - d * d * twsum, g0);
                wide prod = 0, tprod = 0, tlift = 0, tother = 0;
                if (!mul_fits(dsk, bracket, &prod) || !mul_fits(tdsk, bracket, &tprod) || !mul_fits(tprod, (wide)1 << 8, &tlift) || !mul_fits(dsk, tbracket, &tother)) {
                    atomicOr(w.status, REFUSED_KEY);
                }
                const wide pw = div_nearest_by(prod, cdiv2[warp][jj]);
                add_wide(w.cw + (first + r + lo) * S + entry, pw);
                add_wide(w.cw + (first + r + hi_ + 1) * S + entry, -pw);
                const wide tpw = div_nearest_by(tlift + tother, cdiv2[warp][jj]);
                add_wide(tcw + (first + r + lo) * S + entry, tpw);
                add_wide(tcw + (first + r + hi_ + 1) * S + entry, -tpw);
            }
        }
        sum = parts_sum(active ? sum : 0, S, parts);
        tsum = parts_sum(active ? tsum : 0, S, parts);
        if (lane < S) {
            const uint32_t mc = h * n + lane % n;
            const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
            w.dp[slot] = fit64(rel(sum, CONTACT_BACK + g0), w.status);
            tp[slot] = fit64(rel(tsum, CONTACT_BACK + 8 + g0), w.status);
        }
        __syncwarp();
    }
}

// [definition; agent-inferred, November 7] **The key's column return and its tangent over one head** (the host's
// `lock_words`), one warp a source site `j` over its receivers: `δk̃_j += release(Σ_i δs_ij ((D p̂_i) 2^g − D² k̂_j), 32 + g)`
// and its tangent `release(Σ_i [δs'_ij β_ij 2^8 + δs_ij ((D δp̂_i) 2^g − D² δk̂_j)], 40 + g)`, `β_ij` the bracket released by
// the skin's bits, each product checked as the host's.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_energy_tangent_columns(FieldWords w, uint32_t h, const int64_t *uq, const int64_t *up, const int64_t *ds, const wide *tds, int64_t *dq, int64_t *tq) {
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n, classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const uint32_t entry = lane % S, part = lane / S;
    const uint32_t m = entry % n;
    const bool still = skinless(w, h);
    const uint32_t g0 = still ? 0 : MOVE_BITS;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t r = w.site_region[g];
        const uint32_t j = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[(uint64_t)h * w.T + g];
        const uint32_t *poff = w.poff + ((uint64_t)h * w.R + r) * (classes + 1);
        const uint32_t *pmem = w.pmem + ((uint64_t)h * w.T + first) * probe_stride(w);
        const uint32_t *olist = w.olist + w.ostart[r];
        const uint32_t K = keyed_site(w, g) ? receiver_len(off, poff, w.ostart[r + 1] - w.ostart[r], c, definite_site(w, g)) : 0;
        const int64_t *dsc = ds + w.region_eoff[r] + j;
        const wide *tdsc = tds + w.region_eoff[r] + j;
        const wide qj = (wide)w.qf[((uint64_t)h * w.T + g) * S + entry], tkj = (wide)uq[((uint64_t)h * w.T + g) * S + entry];
        wide sk = 0, tsk = 0;
        if (part < parts) {
            for (uint32_t k = part; k < K; k += parts) {
                const uint32_t i = receiver_at(members, off, pmem, poff, olist, c, j, sites, k);
                if (i == UINT32_MAX || skipped_row(w, first + i)) {
                    continue;
                }
                const uint64_t at = (uint64_t)i * sites;
                const uint32_t gap = j > i ? j - i : i - j;
                const wide dec = skin_raw(w, h, m, first + i, g, gap);
                const uint64_t ri = ((uint64_t)h * w.T + first + i) * S + entry;
                const wide bracket = rel(((dec * (wide)w.pq[ri]) << g0) - dec * dec * qj, g0);
                const wide tbracket = rel(((dec * (wide)up[ri]) << g0) - dec * dec * tkj, g0);
                wide prod = 0, tprod = 0, tlift = 0, tother = 0;
                if (!mul_fits((wide)dsc[at], bracket, &prod) || !mul_fits(tdsc[at], bracket, &tprod) || !mul_fits(tprod, (wide)1 << 8, &tlift) || !mul_fits((wide)dsc[at], tbracket, &tother)) {
                    atomicOr(w.status, REFUSED_KEY);
                }
                sk += prod;
                tsk += tlift + tother;
            }
        }
        sk = parts_sum(part < parts ? sk : 0, S, parts);
        tsk = parts_sum(part < parts ? tsk : 0, S, parts);
        if (lane < S) {
            const uint32_t mc = h * n + lane % n;
            const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
            dq[slot] = fit64((wide)dq[slot] + rel(sk, CONTACT_BACK + g0), w.status);
            tq[slot] = fit64((wide)tq[slot] + rel(tsk, CONTACT_BACK + 8 + g0), w.status);
        }
    }
}

// A crowds' difference array `cw` summed over the places and added at the definite sites (the host's `spread_w`),
// `dq = fit64(dq + release(Σ cw, 32 + extra + g))`; one block a region, as `field_spread`.
extern "C" __global__ void field_energy_spread(FieldWords w, uint32_t h, const wide *cw, uint32_t extra, int64_t *dq) {
    __shared__ wide psw[SPREAD_THREADS];
    const bool still = skinless(w, h);
    const uint32_t g0 = still ? 0 : MOVE_BITS;
    const uint32_t S = w.span;
    const uint32_t nchunk = blockDim.x / S;
    const uint32_t x = threadIdx.x % S, ck = threadIdx.x / S;
    const bool live = ck < nchunk;
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t len = (sites + nchunk - 1) / nchunk;
        const uint32_t lo = ck * len, hi = min(sites, lo + len);
        wide sw = 0;
        if (live) {
            for (uint32_t t = lo; t < hi; t++) {
                sw += cw[(first + r + t) * S + x];
            }
            psw[threadIdx.x] = sw;
        }
        __syncthreads();
        if (live) {
            wide run = 0;
            for (uint32_t c = 0; c < ck; c++) {
                run += psw[c * S + x];
            }
            for (uint32_t t = lo; t < hi; t++) {
                run += cw[(first + r + t) * S + x];
                if (definite_site(w, first + t)) {
                    const uint32_t m = h * w.n + x % w.n;
                    const uint64_t slot = (first + t) * w.M2 + (x < w.n ? m : w.M + m);
                    dq[slot] = fit64((wide)dq[slot] + rel(run, CONTACT_BACK + extra + g0), w.status);
                }
            }
        }
        __syncthreads();
    }
}

// [definition; agent-inferred, November 7] **The unit power's return differentiated** (the host's `energy_tangent`): at each
// head and site of a word `ŵ` at power `‖w̃‖` (its framed tangent `δw̃`, its unit tangent `δŵ`, the force `f` on it and the
// force's tangent `δf`, `[t][2M]`), `J δf − release(div_nearest(−(δŵ⟨ŵ, f⟩ + ŵ⟨δŵ, f⟩) 2^16, 2n‖w̃‖), 40) −
// release(div_nearest(−(J f)⟨ŵ, δw̃⟩ 2^16, 2n‖w̃‖), 40)` into its framed chart slot, zero at a word of no power. One warp a
// head and a site.
extern "C" __global__ void field_energy_unit_tangent_back(FieldWords w, const int64_t *unit, const wide *scale, const int64_t *du, const int64_t *dwt, const int64_t *force, const int64_t *tforce, int64_t *out) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    const uint32_t S = w.span;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        const uint32_t h = hs / w.T;
        const uint64_t t = hs % w.T;
        const wide s = scale[hs];
        const bool live = lane < S;
        const uint64_t slot = t * w.M2 + (lane < w.n ? h * w.n + lane : w.M + h * w.n + lane - w.n);
        if (s == 0) {
            if (live) {
                out[slot] = 0;
            }
            continue;
        }
        const wide u = live ? (wide)unit[hs * S + lane] : 0;
        const wide fv = live ? (wide)force[slot] : 0, tv = live ? (wide)tforce[slot] : 0;
        const wide d_u = live ? (wide)du[hs * S + lane] : 0, dw_ = live ? (wide)dwt[hs * S + lane] : 0;
        const wide a_wf = warp_sum(u * fv), b_df = warp_sum(d_u * fv), c_wd = warp_sum(u * dw_), dot_t = warp_sum(u * tv);
        const wide mean_f = div_nearest(a_wf, (wide)S), mean_t = div_nearest(dot_t, (wide)S);
        if (!live) {
            continue;
        }
        const wide jf = fit64(div_nearest((fv - rel(mean_f * u, 2 * FACE_BITS)) << FACE_BITS, s), w.status);
        const wide base = fit64(div_nearest((tv - rel(mean_t * u, 2 * FACE_BITS)) << FACE_BITS, s), w.status);
        const wide den = (wide)S * s;
        const wide s1 = d_u * a_wf + u * b_df;
        const wide corr = rel(div_nearest(-(s1 << FACE_BITS), den), 2 * FACE_BITS + 8) + rel(div_nearest(-((jf * c_wd) << FACE_BITS), den), 2 * FACE_BITS + 8);
        out[slot] = fit64(base + corr, w.status);
    }
}

// The pair's force tangent (the host's `energy_tangent`): each drive's force linear in the other's tangent drive, `δa_t = c ⊙
// δb_s` and `δb_s = c ⊙ δa_t` along the strand (§16.34), released to `2^(−24)`. One thread a site and a pair of contacts.
extern "C" __global__ void field_energy_pair_tangent(FieldWords w, uint64_t pair_c, const int64_t *ta, const int64_t *tb, int64_t *da, int64_t *db) {
    const uint32_t half = w.f / 2;
    const uint64_t cells = (uint64_t)w.T * half;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / half, e = c % half;
        const uint64_t re = t * w.f + e, im = re + half;
        const wide cr = w.theta[pair_c + e], ci = w.theta[pair_c + half + e];
        const uint64_t s = strand_mate(w, t, e);
        if (s == UINT64_MAX) {
            da[re] = 0;
            da[im] = 0;
        } else {
            const wide br = tb[s * w.f + e], bi = tb[s * w.f + half + e];
            da[re] = fit64(rel(cr * br + ci * bi, MATERIAL_BITS), w.status);
            da[im] = fit64(rel(ci * br - cr * bi, MATERIAL_BITS), w.status);
        }
        const uint64_t p = strand_mate(w, t, e ^ 1);
        if (p == UINT64_MAX) {
            db[re] = 0;
            db[im] = 0;
        } else {
            const wide ar = ta[p * w.f + e], ai = ta[p * w.f + half + e];
            db[re] = fit64(rel(cr * ar + ci * ai, MATERIAL_BITS), w.status);
            db[im] = fit64(rel(ci * ar - cr * ai, MATERIAL_BITS), w.status);
        }
    }
}

// `w = s ⊙ λ` on `2^(−24)` (`release(s λ, 16)`, `s` each lane's scale) at the regions whose tick stood (`halvings[r]`), zero
// at the rest.
extern "C" __global__ void field_energy_scaled(FieldWords w, const wide *scale, const int64_t *lambda, const uint32_t *halvings, int64_t *wv) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    const uint32_t lw = w.D / w.lanes;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        wv[c] = halvings[w.site_region[t]] == UINT32_MAX ? 0 : fit64(rel(scale[t * w.lanes + i / lw] * (wide)lambda[c], FACE_BITS), w.status);
    }
}

// A tick's letters' covectors (the host's `energy_reverse`): at the regions whose tick stood at `h` halvings, `own +=
// release(R w, h)`, `before_t += release(w_(t+1), h)`, `after_t += release(w_(t−1), h)` (within the region) and `moment +=
// release(Cᵀ w + δp', h)`, each addition checked.
extern "C" __global__ void field_energy_reverse_letters(FieldWords w, const int64_t *wv, const int64_t *lift, const int64_t *chart, const int64_t *probe, const uint32_t *halvings, int64_t *own, int64_t *before, int64_t *after, int64_t *moment) {
    const uint64_t rows = (uint64_t)w.T * w.D;
    const uint64_t cells = rows + (uint64_t)w.T * w.M2;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        if (c < rows) {
            const uint64_t t = c / w.D, i = c % w.D;
            const uint32_t h = halvings[w.site_region[t]];
            if (h == UINT32_MAX) {
                continue;
            }
            own[c] = fit64((wide)own[c] + rel((wide)lift[c], h), w.status);
            if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
                before[c] = fit64((wide)before[c] + rel((wide)wv[(t + 1) * w.D + i], h), w.status);
            }
            if (w.site_pos[t] > 0) {
                after[c] = fit64((wide)after[c] + rel((wide)wv[(t - 1) * w.D + i], h), w.status);
            }
        } else {
            const uint64_t k = c - rows;
            const uint32_t h = halvings[w.site_region[k / w.M2]];
            if (h == UINT32_MAX) {
                continue;
            }
            moment[k] = fit64((wide)moment[k] + rel((wide)chart[k] + (wide)probe[k], h), w.status);
        }
    }
}

// `λ = λ' + 2^(−h) (r̂ ⟨λ', F⟩/W + J δF)` in place (the host's `energy_reverse`), each lane's at the regions whose tick stood:
// `release(release(r̂ div_nearest(⟨λ', F⟩, W), 40) + (J δF), h)` added, checked. One warp a site.
extern "C" __global__ void field_energy_lambda(FieldWords w, const int32_t *read, const int64_t *force, const int64_t *jt, const uint32_t *halvings, int64_t *lambda) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint32_t lw = w.D / w.lanes;
    for (uint64_t t = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; t < w.T; t += warps) {
        const uint32_t h = halvings[w.site_region[t]];
        if (h == UINT32_MAX) {
            continue;
        }
        for (uint32_t k = 0; k < w.lanes; k++) {
            const uint64_t at = t * w.D + k * lw;
            wide dot = 0;
            for (uint32_t i = lane; i < lw; i += 32) {
                dot += (wide)lambda[at + i] * (wide)force[at + i];
            }
            dot = warp_sum(dot);
            const wide mean = div_nearest(dot, (wide)lw);
            for (uint32_t i = lane; i < lw; i += 32) {
                const wide radial = rel((wide)read[at + i] * mean, 2 * FACE_BITS + 8);
                lambda[at + i] = fit64((wide)lambda[at + i] + rel(radial + (wide)jt[at + i], h), w.status);
            }
        }
    }
}

// The opening's letters' covectors (the host's `energy_reverse`): `own += λ⁰`, `before_t += λ⁰_(t+1)`, `after_t += λ⁰_(t−1)`
// (within the region) and `moment += Cᵀ λ⁰` (`chart`), each addition checked.
extern "C" __global__ void field_energy_opening_letters(FieldWords w, const int64_t *lambda, const int64_t *chart, int64_t *own, int64_t *before, int64_t *after, int64_t *moment) {
    const uint64_t rows = (uint64_t)w.T * w.D;
    const uint64_t cells = rows + (uint64_t)w.T * w.M2;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        if (c < rows) {
            const uint64_t t = c / w.D, i = c % w.D;
            own[c] = fit64((wide)own[c] + (wide)lambda[c], w.status);
            if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
                before[c] = fit64((wide)before[c] + (wide)lambda[(t + 1) * w.D + i], w.status);
            }
            if (w.site_pos[t] > 0) {
                after[c] = fit64((wide)after[c] + (wide)lambda[(t - 1) * w.D + i], w.status);
            }
        } else {
            const uint64_t k = c - rows;
            moment[k] = fit64((wide)moment[k] + (wide)chart[k], w.status);
        }
    }
}

// `x = −x` (`λ^K = −J F^K`).
extern "C" __global__ void field_energy_negate(FieldWords w, int64_t *x, uint64_t cells) {
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        x[c] = -x[c];
    }
}
