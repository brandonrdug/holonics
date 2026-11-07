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
// energy back. The face at an open site is the energy's force on its letter at the last state (`field_energy_dm`,
// `field_energy_face` after the encoding's tied face).
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

// The moment's covector of the face (the host's `energy_pass`): `dm = release(Cᵀ r̂_t, 16) + δp_t` (`[t][2M]`, held on 128
// bits for the moments' return), `C` the moment's chart into the face and `δp` the probes' share of the force.
extern "C" __global__ void field_energy_dm(FieldWords w, uint64_t mface, const int32_t *read, const int64_t *dp, wide *dm) {
    const uint64_t cells = (uint64_t)w.T * w.M2;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.M2, k = c % w.M2;
        wide sum = 0;
        for (uint32_t o = 0; o < w.D; o++) {
            sum += (wide)w.theta[mface + (uint64_t)o * w.M2 + k] * (wide)read[t * w.D + o];
        }
        const int64_t back = fit64(rel(sum, FACE_BITS), w.status);
        dm[c] = fit64((wide)back + (wide)dp[c], w.status);
    }
}

// [definition; agent-inferred, November 6] **The face is the energy's force on a letter** (the host's `energy_pass`): at
// each unresolved site, onto the encoding's tied face `z(a)`, the strand rows against the sites they reach,
// `release(⟨E₋(a), r̂_(t+1)⟩ + ⟨E₊(a), r̂_(t−1)⟩, 16)`, and the moment's part `release(Σ_k E⁻_m(a)_k δb_t[k] + E⁺_m(a)_k δa_t[k],
// 24)` through the moment's return (`d_before`, `d_after`, `[u][t]` pairs on 128 bits).
extern "C" __global__ void field_energy_face(FieldWords w, const int32_t *read, const wide *dbefore, const wide *dafter, uint32_t tm, uint64_t mbefore, uint64_t mafter, int64_t *z) {
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
        wide part = 0;
        for (uint32_t k = 0; k < 2 * tm; k++) {
            const uint32_t u = k < tm ? k : k - tm;
            const uint64_t at = (uint64_t)u * 2 * w.T + 2 * t + (k < tm ? 0 : 1);
            part += (wide)w.theta[mbefore + a * 2 * tm + k] * dbefore[at] + (wide)w.theta[mafter + a * 2 * tm + k] * dafter[at];
        }
        z[c] = fit64((wide)z[c] + rel(strand, FACE_BITS) + rel(part, COVECTOR_BITS), w.status);
    }
}
