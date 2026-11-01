// The field's card realization (`holonics::hnn::tower::field`, records
// `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`,
// §7, and `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
// §6): one constitution iterated over every site of every region of a batch at once, and its exact
// reverse, bit for bit the host's `Field::pass` and `Field::reverse`.
//
// [definition; agent-inferred, November 1] **The field disperses.** Each head reads one word a site
// (the probe and the key at once); a site meets its support, its near field (`0 < |i − j| < NEAR`)
// and the other members of its resonance class (its word's half-turn sheets), each at the octave
// falloff `⌊log₂ |i − j|⌋` bits. The classes are listed by one stable counting sort a head and region
// (`field_classes`), and every contact kernel visits only the support. The weights and the contact's
// return keep the dense address `[i][j]` of the region's block, written and read only on the
// support, so a column's reads find `e_ij` without an index.
//
// [definition; agent-inferred, November 1] The launch follows regions × sites × heads, never a padded
// window: a site is its global index in the batch (`site_region`, `site_pos`), a contact row is a head
// and a site, and a region's pairs are its own block of the weight store (`region_eoff`). Every
// product's remainder below its grain is released to the nearest numerator (`rel`) and every sum is an
// integer sum, so a row read by 32 lanes, a covector summed over sites or a sum over regions gives the
// host's bits whatever the order. A contact row is read in two passes over its keys (the peak; then
// the weights, their mass and the current's numerators) and divided once by its mass: an online
// rescaling would round each partial sum at a peak that later moves, and the bits would follow the
// tile order.

#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

#define FACE_BITS 16
#define MATERIAL_BITS 24
#define MOVE_BITS 30
#define COVECTOR_BITS 24
#define UNIT_BITS 62
#define WEIGHT_BITS_FROM 22
// A weight's grain below its row's peak (the host's `WEIGHT_BITS`), and the half a narrow value sum
// splits it at: `e ≤ 2^WEIGHT_BITS` is `2^WEIGHT_HALF e_h + e_l` with `e_h ≤ 2^WEIGHT_HALF`.
#define WEIGHT_BITS (UNIT_BITS - WEIGHT_BITS_FROM)
#define WEIGHT_HALF (WEIGHT_BITS / 2)
static_assert(WEIGHT_BITS % 2 == 0 && WEIGHT_HALF < 31, "a weight splits into two halves of a 32-bit product");
#define CARRIED_BITS 70
#define CONTACT_BACK 32
// The contact's covector grain, `δz` on `2^(−40)` (the host's `CONTACT_BITS`).
#define CONTACT_BITS 40

// The near field, `lcm(2, 3)` (the host's `NEAR`): a site meets the sites closer than it whatever
// their classes, the `2(NEAR − 1)` nearest a site's first support entries.
#define NEAR 6
#define NEAR_SLOTS (2 * (NEAR - 1))

#define REFUSED_CARRIER 1u
#define REFUSED_WORD64 2u
#define REFUSED_WORD32 4u
#define REFUSED_SHIFT 8u

// -------------------------------------------------------------------------------------------
// the host's integer law
//
// [agent-inferred, November 1] The field's image restates the release, the nearest quotient, the
// carriers' refusals, the root and the exponential's face that `tower.cu` carries, so the tower's
// image, read to parity on its own declarations, is left as it was; both are the host's law (`release`,
// `div_nearest`, `fit64`, `fit32`, `u128::isqrt`, `Exponential::below_one` through its resident face), and each image's parity
// against the host reads that equality.

// `x` released `bits` coarser, to the nearest numerator, half away from zero (`release`).
__device__ __forceinline__ wide rel(wide x, unsigned bits) {
    if (bits == 0) {
        return x;
    }
    const wide half = (wide)1 << (bits - 1);
    return x >= 0 ? (x + half) >> bits : -((-x + half) >> bits);
}

// `x / k` to the nearest integer, half away from zero, `k > 0` (`div_nearest`).
__device__ __forceinline__ wide div_nearest(wide x, wide k) {
    const wide n = (x >= 0 ? x : -x) + k / 2;
    if (n <= (wide)INT64_MAX && k <= (wide)INT64_MAX) {
        const wide q = (wide)((uint64_t)n / (uint64_t)k);
        return x >= 0 ? q : -q;
    }
    return x >= 0 ? n / k : -(n / k);
}

// [agent-inferred, November 1] **An exact quotient by an invariant divisor.** A contact row's
// return divides one product a pair by the row's mass; a 128-bit division is a long software routine
// on the card, so the divisor is read once a row as its normalized form `d = k 2^s` and reciprocal
// `v = ⌊(2^128 − 1)/d⌋ − 2^64` (Möller and Granlund, "Improved division by invariant integers",
// 2011, Algorithm 4), and each division is two of its steps: the quotient is the integer `⌊n/k⌋`,
// whatever the route, so the bits are `div_nearest`'s.
struct Divisor {
    uint64_t k, d, v;
    uint32_t s;
};

__device__ __forceinline__ Divisor divisor_of(uint64_t k) {
    Divisor q;
    q.k = k;
    q.s = (uint32_t)__clzll((long long)k);
    q.d = k << q.s;
    // ⌊(2^128 − 1)/d⌋ − 2^64 = ⌊((2^64 − 1 − d) 2^64 + 2^64 − 1)/d⌋, below 2^64 since d ≥ 2^63.
    q.v = (uint64_t)((((uwide)(~q.d)) << 64 | (uwide)UINT64_MAX) / (uwide)q.d);
    return q;
}

// `⌊(u1 2^64 + u0)/d⌋` and its remainder, `u1 < d`, `d` normalized (Algorithm 4).
__device__ __forceinline__ uint64_t divide_word(uint64_t u1, uint64_t u0, const Divisor &q, uint64_t *rem) {
    const uwide p = (uwide)q.v * (uwide)u1 + (((uwide)u1 << 64) | (uwide)u0);
    uint64_t q1 = (uint64_t)(p >> 64) + 1;
    const uint64_t q0 = (uint64_t)p;
    uint64_t r = u0 - q1 * q.d;
    if (r > q0) {
        q1 -= 1;
        r += q.d;
    }
    if (r >= q.d) {
        q1 += 1;
        r -= q.d;
    }
    *rem = r;
    return q1;
}

// `⌊n/k⌋` for a 128-bit `n`.
__device__ __forceinline__ uwide divide_by(uwide n, const Divisor &q) {
    const uint64_t nh = (uint64_t)(n >> 64), nl = (uint64_t)n;
    uint64_t n2 = 0, n1 = nh, n0 = nl;
    if (q.s != 0) {
        n2 = nh >> (64 - q.s);
        n1 = (nh << q.s) | (nl >> (64 - q.s));
        n0 = nl << q.s;
    }
    uint64_t r;
    const uint64_t qh = divide_word(n2, n1, q, &r);
    const uint64_t ql = divide_word(r, n0, q, &r);
    return ((uwide)qh << 64) | (uwide)ql;
}

// `div_nearest(x, k)` by a read divisor.
__device__ __forceinline__ wide div_nearest_by(wide x, const Divisor &q) {
    const uwide n = (uwide)(x >= 0 ? x : -x) + (uwide)(q.k / 2);
    const wide quotient = (wide)divide_by(n, q);
    return x >= 0 ? quotient : -quotient;
}

// The ring sum's atomic step on `Z/2^128` (the host's wrapping `i128` sum): the low word added
// atomically, and the high word with the low word's carry, so any order of additions leaves the same
// 128 bits.
__device__ __forceinline__ void add_wide(wide *at, wide v) {
    unsigned long long *word = (unsigned long long *)at;
    const unsigned long long lo = (unsigned long long)(uint64_t)v;
    const unsigned long long hi = (unsigned long long)(uint64_t)((uwide)v >> 64);
    const unsigned long long old = atomicAdd(word, lo);
    atomicAdd(word + 1, hi + (old + lo < old ? 1ull : 0ull));
}

__device__ __forceinline__ int64_t fit64(wide v, uint32_t *st) {
    if (v > (wide)INT64_MAX || v < (wide)INT64_MIN) {
        atomicOr(st, REFUSED_WORD64);
        return 0;
    }
    return (int64_t)v;
}

__device__ __forceinline__ int32_t fit32(wide v, uint32_t *st) {
    if (v > (wide)INT32_MAX || v < (wide)INT32_MIN) {
        atomicOr(st, REFUSED_WORD32);
        return 0;
    }
    return (int32_t)v;
}

__device__ __forceinline__ uint64_t mag64(int64_t v) {
    return v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
}

__device__ uwide isqrt128(uwide n) {
    uwide res = 0;
    uwide bit = (uwide)1 << 126;
    while (bit > n) {
        bit >>= 2;
    }
    while (bit != 0) {
        if (n >= res + bit) {
            n -= res + bit;
            res = (res >> 1) + bit;
        } else {
            res >>= 1;
        }
        bit >>= 2;
    }
    return res;
}

// `below_one` read through the exponential's resident face (`field_exponential`): the same split into
// whole and fraction, the same shift.
__device__ __forceinline__ uint64_t below_one_face(wide x, const uint64_t *face, uint32_t digits) {
    const wide m = -x;
    const wide whole = m >> digits;
    const uint64_t frac = (uint64_t)(m & (((wide)1 << digits) - 1));
    const wide shift = frac == 0 ? whole : whole + 1;
    const uint64_t rest = frac == 0 ? 0 : ((uint64_t)1 << digits) - frac;
    const uint64_t value = face[rest];
    const uint64_t shifted = shift >= 64 ? 0 : value >> (uint32_t)shift;
    return shifted == 0 ? 1 : shifted;
}

// The binary length of a magnitude (`0` for zero).
__device__ __forceinline__ uint32_t bit_length(uint64_t m) {
    return m == 0 ? 0 : 64 - __clzll((long long)m);
}

// `⌈log₂ x⌉` (`0` for `x ≤ 1`).
__device__ __forceinline__ uint32_t ceil_log2(uint64_t x) {
    return x <= 1 ? 0 : 64 - __clzll((long long)(x - 1));
}

__device__ __forceinline__ uwide shfl_wide(uwide v, int o) {
    const uint64_t lo = __shfl_xor_sync(0xffffffffu, (uint64_t)v, o);
    const uint64_t hi = __shfl_xor_sync(0xffffffffu, (uint64_t)(v >> 64), o);
    return ((uwide)hi << 64) | lo;
}

// The warp's ring sum (`Z/2^128`, the host's wrapping `i128` sum); every lane holds it.
__device__ __forceinline__ wide warp_sum(wide v) {
    uwide u = (uwide)v;
    for (int o = 16; o > 0; o >>= 1) {
        u += shfl_wide(u, o);
    }
    return (wide)u;
}

__device__ __forceinline__ uint64_t warp_sum_u64(uint64_t v) {
    for (int o = 16; o > 0; o >>= 1) {
        v += __shfl_xor_sync(0xffffffffu, v, o);
    }
    return v;
}

__device__ __forceinline__ int64_t warp_max_signed(int64_t v) {
    uint64_t key = (uint64_t)v ^ ((uint64_t)1 << 63);
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, key, o);
        key = w > key ? w : key;
    }
    return (int64_t)(key ^ ((uint64_t)1 << 63));
}

__device__ __forceinline__ uint64_t warp_max_u64(uint64_t v) {
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, v, o);
        v = w > v ? w : v;
    }
    return v;
}

// -------------------------------------------------------------------------------------------
// the batch

// The batch's declaration, material, rings, regions and the tick's carriers. Every entry takes it by
// value; a tick's launches set its carriers.
struct FieldWords {
    uint32_t D, H, n, still, f, A, frames;
    // The gain's shift, negative where it amplifies (`FieldDeclaration::score_shift`), the classes'
    // shells `b` (`class_trits`) and their count `3^b`.
    int32_t beta;
    uint32_t ctrits, nclasses;
    // The contact covector's carrier: `|δs| < 2^dsbits` (`FieldDeclaration::contact_return_bits`).
    uint32_t dsbits;
    uint32_t M, M2, span, digits;
    uint32_t T, R;
    uint64_t E;
    // `ln 2` on `2^(−30)`, the weights' return reads it (two words of a signed 128-bit value).
    uint64_t ln2_lo, ln2_hi;
    const int32_t *theta;
    uint64_t enc, enc_before, enc_after, q, q_bias, v, v_bias, out, out_bias, a, a_bias, b, b_bias, w, w_bias, read, read_bias;
    uint64_t rq, rv, rout, ra, rb, rw, rread;
    const int64_t *phasor;
    const uint64_t *ring_off;
    const uint64_t *ring_n;
    // Each turned slot's skin decay on `2^(−30)` at every distance within the reach, `[slot][d]`
    // with stride `dreach` (`Field::decays`).
    const int64_t *decay;
    uint64_t dreach;
    const uint64_t *roots;
    const uint32_t *site_region;
    const uint32_t *site_pos;
    const uint32_t *region_off;
    const uint64_t *region_eoff;
    const uint32_t *classes;
    const uint8_t *unresolved;
    // The carried mixtures: site `t`'s shares are `mix_class`, `mix_share` over `mix_off[t]..mix_off[t + 1]`
    // (none where the site is not carried).
    const uint32_t *mix_off;
    const uint32_t *mix_class;
    const uint32_t *mix_share;
    uint32_t *status;
    // The site pairs the contact met (`Σ |S_i^h|` over every row and tick).
    unsigned long long *met;
    // The tick's carriers the frame, the contact and the pair contact read and write (the charts'
    // reads and scales are passed to their own launches).
    int64_t *x;
    int64_t *qkv;
    int64_t *qf, *vf;
    // The tick's classes `[h][t]`, each region's class offsets `[h][r][2·3^b + 1]` (relative to its
    // members; class `c`'s known members at `2c`, its others at `2c + 1`) and its members `[h][t]`
    // (places within the region, ascending within each).
    uint32_t *cls;
    uint32_t *class_off;
    uint32_t *members;
    uint64_t *e;
    uint64_t *mass;
    int64_t *y;
    int64_t *pa, *pb, *pc;
    // The tick's magnitude (the binary length of the largest unit word, `bits[0]`) and the
    // exponential's resident face.
    uint32_t *bits;
    const uint64_t *face;
};

// The frame of local mode `l` of head `h` at site `t`: the identity in a head of a still ring set
// (`h mod frames < still`), the mode's ring in a turned one (slot `l (frames − still) + set − still`).
__device__ __forceinline__ void frame_of(const FieldWords &w, uint32_t t, uint32_t h, uint32_t l, wide *ur, wide *ui) {
    const uint32_t set = h % w.frames;
    if (set < w.still) {
        *ur = (wide)1 << MOVE_BITS;
        *ui = 0;
        return;
    }
    const uint32_t slot = l * (w.frames - w.still) + set - w.still;
    const uint64_t at = w.ring_off[slot] + t % w.ring_n[slot];
    *ur = w.phasor[2 * at];
    *ui = w.phasor[2 * at + 1];
}

// [definition; agent-inferred, November 1] **The skin decay of local mode `l` of head `h` across `d`
// sites** (`Field::decay`): `e^(−2π d/n)` on `2^(−30)` in a turned head; a still head's is the exact
// `1`, read by the callers as no decay at all.
__device__ __forceinline__ wide decay_of(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d) {
    const uint32_t set = h % w.frames;
    return w.decay[(uint64_t)(l * (w.frames - w.still) + set - w.still) * w.dreach + d];
}

// A known site: resolved and carrying no mixture (its class arrived). Past the near field two
// class-mates meet only where one of them is known (`ClassLists`: far contacts are bipartite).
__device__ __forceinline__ bool known_site(const FieldWords &w, uint64_t g) {
    return w.unresolved[g] == 0 && w.mix_off[g] == w.mix_off[g + 1];
}

// A head of a still ring set (its modes unframed, undecayed).
__device__ __forceinline__ bool still_head(const FieldWords &w, uint32_t h) {
    return h % w.frames < w.still;
}

// A value carried across a pair by its skin decay: `release(D v, 30)` in a turned head, `v` in a still
// one (`decayed`).
__device__ __forceinline__ wide carried(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d, int64_t v) {
    return still_head(w, h) ? (wide)v : rel(decay_of(w, h, l, d) * (wide)v, MOVE_BITS);
}

// [agent-inferred, November 1] **The exponential's resident face**: `face[rest]` is the product of the
// roots `below_one` multiplies for the binary digits of `rest`, each `rest` of the `2^digits` read by
// the same loop on the card, so a weight read through the face is `below_one`'s bits exactly (a
// navigator's resident face at its declared grain, never a table of answers). It replaces up to
// `digits` dependent 64-bit products a pair by one read of `2^digits` words (512 KiB at 16 digits).
extern "C" __global__ void field_exponential(FieldWords w, uint64_t *face) {
    const uint64_t cells = (uint64_t)1 << w.digits;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        uint64_t value = (uint64_t)1 << UNIT_BITS;
        for (uint32_t i = 0; i < w.digits; i++) {
            if (c & ((uint64_t)1 << (w.digits - 1 - i))) {
                const uint64_t lo = value * w.roots[i];
                const uint64_t hi = __umul64hi(value, w.roots[i]);
                value = (hi << (64 - UNIT_BITS)) | (lo >> UNIT_BITS);
            }
        }
        face[c] = value;
    }
}

// A site's encoding row: its class, or the unresolved row.
__device__ __forceinline__ uint64_t row_of(const FieldWords &w, uint64_t t) {
    return w.unresolved[t] ? w.A : w.classes[t];
}

// Site `s`'s opening term in the encoding at `base`, entry `i`: its row, or the mixture of its carried
// shares' rows `release(Σ_a w_a E(a), 16)` (`Field::opening_term`).
__device__ __forceinline__ int64_t opening_term(const FieldWords &w, uint64_t base, uint64_t s, uint64_t i) {
    const uint32_t from = w.mix_off[s], to = w.mix_off[s + 1];
    if (from == to) {
        return w.theta[base + row_of(w, s) * w.D + i];
    }
    wide sum = 0;
    for (uint32_t k = from; k < to; k++) {
        sum += (wide)w.mix_share[k] * (wide)w.theta[base + (uint64_t)w.mix_class[k] * w.D + i];
    }
    return (int64_t)rel(sum, FACE_BITS);
}

// A site's opening face `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))`: its row of the encoding (or its
// mixture's) with its strand neighbours' rows of theirs, a neighbour only within the site's own region
// (a site at its region's first place has none before it; the next site is the region's own when its
// place is not the first).
extern "C" __global__ void field_open(FieldWords w) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        int64_t x = opening_term(w, w.enc, t, i);
        if (w.site_pos[t] > 0) {
            x += opening_term(w, w.enc_before, t - 1, i);
        }
        if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
            x += opening_term(w, w.enc_after, t + 1, i);
        }
        w.x[c] = x;
    }
}

// `r̂ = r / ‖r‖_rms` on `2^(−16)` and `‖r‖_rms` (`ratio_to_power`): one warp a site.
extern "C" __global__ void field_chart(FieldWords w, const int64_t *x, int32_t *read, wide *scale, uint32_t only_unresolved) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    for (uint64_t t = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; t < w.T; t += warps) {
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        const int64_t *xt = x + t * w.D;
        wide power = 0;
        for (uint32_t i = lane; i < w.D; i += 32) {
            power += (wide)xt[i] * (wide)xt[i];
        }
        power = warp_sum(power);
        const wide s = (wide)isqrt128((uwide)(power / (wide)w.D));
        for (uint32_t i = lane; i < w.D; i += 32) {
            read[t * w.D + i] = s == 0 ? 0 : fit32(div_nearest((wide)xt[i] << FACE_BITS, s), w.status);
        }
        if (lane == 0) {
            scale[t] = s;
        }
    }
}

// `out[t][o] = release(Σ_i W[o][i] x[t][i] + bias[o] 2^24, 24)` (`affine`): the host's carrier bound
// `wmax · xmax · (cols + 1)` refused at `2^126`, the sum in 64 bits below `2^62` and in 128 otherwise
// (the same integer either way). With `add`, the result is added to `add[t][o]` (the residual).
template <typename X>
__device__ void affine(const FieldWords &w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const X *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    const uint64_t cells = (uint64_t)w.T * rows;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / rows, o = c % rows;
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        const X *xt = x + t * x_stride;
        uint64_t xmax = 0;
        for (uint32_t i = 0; i < cols; i++) {
            const uint64_t m = mag64((int64_t)xt[i]);
            xmax = m > xmax ? m : xmax;
        }
        const uwide terms = (uwide)wmax * (uwide)xmax * (uwide)(cols + 1);
        if (terms >= ((uwide)1 << 126)) {
            atomicOr(w.status, REFUSED_CARRIER);
            continue;
        }
        const int32_t *row = w.theta + weight + o * cols;
        wide sum;
        if (terms < ((uwide)1 << 62)) {
            int64_t s = 0;
            for (uint32_t i = 0; i < cols; i++) {
                s += (int64_t)row[i] * (int64_t)xt[i];
            }
            sum = s;
        } else {
            sum = 0;
            for (uint32_t i = 0; i < cols; i++) {
                sum += (wide)row[i] * (wide)xt[i];
            }
        }
        sum += (wide)w.theta[bias + o] << MATERIAL_BITS;
        const int64_t v = fit64(rel(sum, MATERIAL_BITS), w.status);
        if (add) {
            add[t * out_stride + o] = fit64((wide)add[t * out_stride + o] + (wide)v, w.status);
        } else {
            out[t * out_stride + o] = v;
        }
    }
}

extern "C" __global__ void field_affine_x32(FieldWords w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const int32_t *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    affine<int32_t>(w, weight, bias, wmax, rows, cols, x, x_stride, out, out_stride, add, only_unresolved);
}

extern "C" __global__ void field_affine_x64(FieldWords w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const int64_t *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    affine<int64_t>(w, weight, bias, wmax, rows, cols, x, x_stride, out, out_stride, add, only_unresolved);
}

// The frame, by head: `w̃ = U ⊙ w` and so for the values, `[h][t][2n]` real parts then imaginary,
// each product released to `2^(−16)`. The word is `qkv[t][0..2M]`, the value `qkv[t][2M..4M]`.
extern "C" __global__ void field_frame(FieldWords w) {
    const uint64_t cells = (uint64_t)w.H * w.T * w.n;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t li = c % w.n;
        const uint64_t t = (c / w.n) % w.T;
        const uint32_t h = c / ((uint64_t)w.n * w.T);
        const uint32_t m = h * w.n + li;
        wide ur, ui;
        frame_of(w, w.site_pos[t], h, li, &ur, &ui);
        const uint64_t at = ((uint64_t)h * w.T + t) * w.span;
        const int64_t *qv = w.qkv + t * 2 * w.M2;
        const wide qr = qv[m], qi = qv[w.M + m];
        const wide vr = qv[w.M2 + m], vi = qv[w.M2 + w.M + m];
        const int64_t q0 = fit64(rel(ur * qr - ui * qi, MOVE_BITS), w.status), q1 = fit64(rel(ui * qr + ur * qi, MOVE_BITS), w.status);
        const int64_t v0 = fit64(rel(ur * vr - ui * vi, MOVE_BITS), w.status), v1 = fit64(rel(ui * vr + ur * vi, MOVE_BITS), w.status);
        w.qf[at + li] = q0;
        w.qf[at + w.n + li] = q1;
        w.vf[at + li] = v0;
        w.vf[at + w.n + li] = v1;
    }
}

// [agent-inferred, November 1] **The contact pairs words at unit power** (`Field::tick`): each head's
// framed word read in place as a ratio to its own power over the head's `2n` reals (`ratio_to_power`,
// on `2^(−16)`), its power kept for the return; one warp a head and a site (`[h][t]`). The binary
// length of the largest unit word is raised into `bits[0]`.
extern "C" __global__ void field_unit(FieldWords w, wide *qscale) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    uint32_t qb = 0;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        int64_t *c = w.qf + hs * w.span;
        wide power = 0;
        for (uint32_t i = lane; i < w.span; i += 32) {
            power += (wide)c[i] * (wide)c[i];
        }
        power = warp_sum(power);
        const wide s = (wide)isqrt128((uwide)(power / (wide)w.span));
        for (uint32_t i = lane; i < w.span; i += 32) {
            const int64_t r = s == 0 ? 0 : (int64_t)fit32(div_nearest((wide)c[i] << FACE_BITS, s), w.status);
            c[i] = r;
            qb = max(qb, bit_length(mag64(r)));
        }
        if (lane == 0) {
            qscale[hs] = s;
        }
    }
    qb = (uint32_t)warp_max_u64(qb);
    if (lane == 0) {
        atomicMax(&w.bits[0], qb);
    }
}

// The return through the word's unit power (`ratio_adjoint`), in place on its framed chart's covector
// `[t][2M]` (head `h`'s slots `h n + l` and `M + h n + l`): `δw̃ = (δŵ − ŵ ⟨ŵ, δŵ⟩/2n) / ‖w̃‖_rms`;
// one warp a head and a site.
extern "C" __global__ void field_unit_back(FieldWords w, const wide *qscale, int64_t *dq) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        const uint32_t h = hs / w.T;
        const uint64_t t = hs % w.T;
        const int64_t *rt = w.qf + hs * w.span;
        const wide s = qscale[hs];
        wide dot = 0;
        for (uint32_t c = lane; c < w.span; c += 32) {
            const uint64_t slot = t * w.M2 + (c < w.n ? h * w.n + c : w.M + h * w.n + c - w.n);
            dot += (wide)rt[c] * (wide)dq[slot];
        }
        dot = warp_sum(dot);
        const wide mean = div_nearest(dot, (wide)w.span);
        for (uint32_t c = lane; c < w.span; c += 32) {
            const uint64_t slot = t * w.M2 + (c < w.n ? h * w.n + c : w.M + h * w.n + c - w.n);
            dq[slot] = s == 0 ? 0 : fit64(div_nearest(((wide)dq[slot] - rel(mean * (wide)rt[c], 2 * FACE_BITS)) << FACE_BITS, s), w.status);
        }
    }
}

// [definition; agent-inferred, November 1] **The resonance classes and their lists** (the dispersing
// field's §2.2, §6 and §12; the host's `ClassLists::of`): one block of one warp a head and a region.
// Each site's class is `Σ_l 3^l σ_l` over the shells of its unframed word's first `b` modes, listed
// under the key `2c` where it is known and `2c + 1` otherwise; the counts are summed in the block's buckets, read as offsets in
// order, and the members placed by a stable counting sort, the region's sites in chunks of 32 in
// order, a lane its rank among the earlier lanes of its class (`__match_any_sync`), so class `c`'s
// members stand in ascending place exactly as the host lists them.
extern "C" __global__ void field_classes(FieldWords w) {
    extern __shared__ uint32_t buckets[];
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t classes = w.nclasses;
    for (uint64_t u = blockIdx.x; u < (uint64_t)w.H * w.R; u += gridDim.x) {
        const uint32_t h = u / w.R, r = u % w.R;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        for (uint32_t c = lane; c < 2 * classes; c += 32) {
            buckets[c] = 0;
        }
        __syncwarp();
        for (uint32_t i = lane; i < sites; i += 32) {
            const uint64_t g = first + i;
            const int64_t *word = w.qkv + g * 2 * w.M2 + h * w.n;
            uint32_t c = 0;
            for (uint32_t l = w.ctrits; l-- > 0;) {
                // The mode's shell (`shell`): the sky plate 2, the ground plate 0, the bridge 1.
                const int64_t re = word[l], im = word[w.M + l];
                const uint64_t quadrature = mag64(im);
                c = 3 * c + (re > 0 && mag64(re) > quadrature ? 2u : re < 0 && mag64(re) > quadrature ? 0u : 1u);
            }
            w.cls[(uint64_t)h * w.T + g] = c;
            atomicAdd(&buckets[2 * c + (known_site(w, g) ? 0u : 1u)], 1u);
        }
        __syncwarp();
        uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        if (lane == 0) {
            uint32_t at = 0;
            for (uint32_t c = 0; c < 2 * classes; c++) {
                const uint32_t n = buckets[c];
                off[c] = at;
                buckets[c] = at;
                at += n;
            }
            off[2 * classes] = at;
        }
        __syncwarp();
        uint32_t *members = w.members + (uint64_t)h * w.T + first;
        for (uint32_t i0 = 0; i0 < sites; i0 += 32) {
            const uint32_t i = i0 + lane;
            const bool live = i < sites;
            const uint32_t c = live ? 2 * w.cls[(uint64_t)h * w.T + first + i] + (known_site(w, first + i) ? 0u : 1u) : 0xFFFFFFFFu;
            const uint32_t peers = __match_any_sync(0xFFFFFFFFu, c);
            const uint32_t rank = __popc(peers & ((1u << lane) - 1u));
            const uint32_t base = live ? buckets[c] : 0;
            __syncwarp();
            if (live) {
                members[base + rank] = i;
                if (rank == 0) {
                    buckets[c] = base + __popc(peers);
                }
            }
            __syncwarp();
        }
        __syncwarp();
    }
}

// [definition; agent-inferred, November 1] Site `i`'s support entry `k` of its region (`ClassLists::support`):
// the near field first (`k < NEAR_SLOTS`, the `NEAR − 1` places before and after it, nearest first),
// then the members of its class past the near field that it may meet (all of them where it is known, the
// known ones where it is not). Returns the source's place, or `UINT32_MAX` where the entry meets no site
// (a near place outside the region, the site itself or a near member of its class).
__device__ __forceinline__ uint32_t support_at(const uint32_t *members, const uint32_t *off, uint32_t c, uint32_t i, uint32_t sites, uint32_t k) {
    if (k < NEAR_SLOTS) {
        const uint32_t d = k / 2 + 1;
        if (k % 2 == 0) {
            return i >= d ? i - d : UINT32_MAX;
        }
        return i + d < sites ? i + d : UINT32_MAX;
    }
    const uint32_t j = members[off[2 * c] + k - NEAR_SLOTS];
    const uint32_t gap = j > i ? j - i : i - j;
    return gap >= NEAR ? j : UINT32_MAX;
}

// A site's support length in entries (`NEAR_SLOTS` near places and its class's members it may meet).
__device__ __forceinline__ uint32_t support_len(const uint32_t *off, uint32_t c, bool known) {
    return NEAR_SLOTS + off[2 * c + (known ? 2 : 1)] - off[2 * c];
}

// `⌊log₂ d⌋`, `d ≥ 1`: the falloff's octave.
__device__ __forceinline__ int64_t octave(uint32_t d) {
    return 31 - __clz(d);
}

// The contact's score of the word `wi` (at unit power, its `span` reals) with site `j`'s, each mode's
// pairing carried by its skin decay across the gap in a turned head (released `46 + β` bits) or bare in
// a still one (`16 + β`), less the falloff `⌊log₂ |i − j|⌋` bits on `2^(−16)` (§2.5, §12).
__device__ __forceinline__ int64_t contact_score(const FieldWords &w, uint32_t h, const int64_t *wi, const int64_t *wj, uint32_t gap, bool narrow) {
    wide s;
    if (!still_head(w, h)) {
        s = 0;
        for (uint32_t l = 0; l < w.n; l++) {
            s += decay_of(w, h, l, gap) * ((wide)wi[l] * (wide)wj[l] + (wide)wi[w.n + l] * (wide)wj[w.n + l]);
        }
        return fit64(rel(s, (uint32_t)((int32_t)FACE_BITS + w.beta) + MOVE_BITS) - ((wide)octave(gap) << FACE_BITS), w.status);
    }
    if (narrow) {
        int64_t n = 0;
        for (uint32_t c = 0; c < w.span; c++) {
            n += (int64_t)(int32_t)wi[c] * (int64_t)(int32_t)wj[c];
        }
        s = n;
    } else {
        s = 0;
        for (uint32_t c = 0; c < w.span; c++) {
            s += (wide)wi[c] * (wide)wj[c];
        }
    }
    return fit64(rel(s, (uint32_t)((int32_t)FACE_BITS + w.beta)) - ((wide)octave(gap) << FACE_BITS), w.status);
}

// The lanes that carry one entry of the span, and the parts of a chunk each lane takes: a lane an
// entry, `32 / span` parts where the span divides the warp (a power of two), else one.
__device__ __forceinline__ uint32_t span_parts(uint32_t span) {
    return 32 % span == 0 ? 32 / span : 1;
}

// A lane's partial of one entry summed over its parts (lanes `entry + p span`).
__device__ __forceinline__ wide parts_sum(wide v, uint32_t span, uint32_t parts) {
    uwide u = (uwide)v;
    for (uint32_t o = span; parts > 1 && o < 32; o <<= 1) {
        u += shfl_wide(u, (int)o);
    }
    return (wide)u;
}

// [definition; agent-inferred, November 1] **The contact, the weights and the current over each
// site's support** (`Field::tick`), one warp a head and a receiving site. Two passes over the support:
// the scores and their peak, its lanes over the support's entries; then the entries again in chunks of
// 32, each lane's weight `release(2^(z − peak), 22)` through the exponential's resident face into the
// warp's shared chunk with its source, the mass, and the numerators `Σ_j e_ij ṽ_j` with the lanes over
// the span's entries (a lane an entry and a part of the chunk). The numerators are divided once by the
// mass and returned to the receiver's frame. The weights are stored at the region block's dense address
// `[i][j]`, on the support only, when a return will read them (`store`); the pairs met are counted.
#define CONTACT_ROWS 8
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact(FieldWords w, uint32_t store) {
    __shared__ uint64_t es[CONTACT_ROWS][32];
    __shared__ uint32_t js[CONTACT_ROWS][32];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span;
    const uint32_t classes = w.nclasses;
    const bool narrow = w.bits[0] <= 31 && 2 * w.bits[0] + ceil_log2(S) <= 62;
    const uint32_t parts = span_parts(S);
    const uint32_t entry = lane % S, part = lane / S;
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[(uint64_t)h * w.T + g];
        const uint32_t K = support_len(off, c, known_site(w, g));
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const int64_t *wi = words + (uint64_t)i * S;
        int64_t peak = INT64_MIN;
        uint32_t met = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, c, i, sites, k);
            if (j != UINT32_MAX) {
                const int64_t z = contact_score(w, h, wi, words + (uint64_t)j * S, j > i ? j - i : i - j, narrow);
                peak = z > peak ? z : peak;
                met += 1;
            }
        }
        peak = warp_max_signed(peak);
        uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        uint64_t mass = 0;
        wide num = 0;
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, c, i, sites, k) : UINT32_MAX;
            uint64_t ej = 0;
            if (j != UINT32_MAX) {
                const int64_t z = contact_score(w, h, wi, words + (uint64_t)j * S, j > i ? j - i : i - j, narrow);
                ej = (uint64_t)rel((wide)below_one_face((wide)z - (wide)peak, w.face, w.digits), WEIGHT_BITS_FROM);
                mass += ej;
                if (store) {
                    erow[j] = ej;
                }
            }
            es[warp][lane] = ej;
            js[warp][lane] = j;
            __syncwarp();
            if (part < parts) {
                for (uint32_t jj = part; jj < 32; jj += parts) {
                    if (es[warp][jj] != 0) {
                        const uint32_t j = js[warp][jj];
                        num += (wide)es[warp][jj] * carried(w, h, entry % w.n, j > i ? j - i : i - j, values[(uint64_t)j * S + entry]);
                    }
                }
            }
            __syncwarp();
        }
        mass = warp_sum_u64(mass);
        met = (uint32_t)warp_sum_u64(met);
        num = parts_sum(part < parts ? num : 0, S, parts);
        // The framed current's entry `entry`, back to the receiver's frame by the lanes of its first part.
        const int64_t y = fit64(div_nearest(num, (wide)mass), w.status);
        const int64_t yi = __shfl_sync(0xFFFFFFFFu, y, (lane + w.n) % 32);
        if (lane == 0) {
            w.mass[(uint64_t)h * w.T + g] = mass;
            atomicAdd(w.met, (unsigned long long)met);
        }
        if (lane < w.n) {
            wide ur, ui;
            frame_of(w, i, h, lane, &ur, &ui);
            const uint32_t m = h * w.n + lane;
            w.y[g * w.M2 + m] = fit64(rel(ur * (wide)y + ui * (wide)yi, MOVE_BITS), w.status);
            w.y[g * w.M2 + w.M + m] = fit64(rel(ur * (wide)yi - ui * (wide)y, MOVE_BITS), w.status);
        }
    }
}

// The pair contact's product `c = release(a ⊙ b, 16)`.
extern "C" __global__ void field_pair(FieldWords w) {
    const uint64_t cells = (uint64_t)w.T * w.f;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        w.pc[c] = fit64(rel((wide)w.pa[c] * (wide)w.pb[c], FACE_BITS), w.status);
    }
}

// Each unresolved site's face from its readout `z` (`[t][A]`): the masses `2^(z − peak)` on `2^(−62)`
// and their total.
extern "C" __global__ void field_face(FieldWords w, const int64_t *z, uint64_t *masses, uwide *totals) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    for (uint64_t t = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; t < w.T; t += warps) {
        if (!w.unresolved[t]) {
            continue;
        }
        const int64_t *zt = z + t * w.A;
        int64_t peak = INT64_MIN;
        for (uint32_t c = lane; c < w.A; c += 32) {
            peak = zt[c] > peak ? zt[c] : peak;
        }
        peak = warp_max_signed(peak);
        wide total = 0;
        for (uint32_t c = lane; c < w.A; c += 32) {
            const uint64_t m = below_one_face((wide)zt[c] - (wide)peak, w.face, w.digits);
            masses[t * w.A + c] = m;
            total += (wide)m;
        }
        total = warp_sum(total);
        if (lane == 0) {
            totals[t] = (uwide)total;
        }
    }
}

// -------------------------------------------------------------------------------------------
// the reverse

// The face's covector `p̂ − [· = class]` on `2^(−24)` at each unresolved site (`covector`), zero at a
// resolved one.
extern "C" __global__ void field_face_covector(FieldWords w, const uint64_t *masses, const uwide *totals, int64_t *dz) {
    const uint64_t cells = (uint64_t)w.T * w.A;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.A, cl = c % w.A;
        if (!w.unresolved[t]) {
            dz[c] = 0;
            continue;
        }
        const uwide total = totals[t];
        const uwide p = (((uwide)masses[c] << COVECTOR_BITS) + total / 2) / total;
        dz[c] = (int64_t)p - (cl == w.classes[t] ? ((int64_t)1 << COVECTOR_BITS) : 0);
    }
}

// `out[t][i] = release(Σ_o W[o][i] y[t][o], 24)` (`transposed`), the weight `rows × cols`; with
// `accumulate` it is added to `out[t][i]` (each addition checked as the host's `fit64`).
extern "C" __global__ void field_transposed(FieldWords w, uint64_t weight, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, int64_t *out, uint32_t accumulate, uint32_t only_unresolved) {
    const uint64_t cells = (uint64_t)w.T * cols;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / cols, i = c % cols;
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        const int64_t *yt = y + t * y_stride;
        wide sum = 0;
        for (uint32_t o = 0; o < rows; o++) {
            sum += (wide)w.theta[weight + (uint64_t)o * cols + i] * (wide)yt[o];
        }
        const int64_t v = fit64(rel(sum, MATERIAL_BITS), w.status);
        out[c] = accumulate ? fit64((wide)out[c] + (wide)v, w.status) : v;
    }
}

// The adjoint of the chart (`ratio_adjoint`) of each site's covector `cov`, added to `base`:
// `dst = base + (cov − r̂ ⟨r̂, cov⟩/D) / ‖r‖_rms`, one warp a site.
extern "C" __global__ void field_ratio_adjoint(FieldWords w, const int32_t *read, const wide *scale, const int64_t *cov, const int64_t *base, int64_t *dst, uint32_t only_unresolved) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    for (uint64_t t = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; t < w.T; t += warps) {
        if (only_unresolved && !w.unresolved[t]) {
            for (uint32_t i = lane; i < w.D; i += 32) {
                dst[t * w.D + i] = base ? base[t * w.D + i] : 0;
            }
            continue;
        }
        const int32_t *rt = read + t * w.D;
        const int64_t *ct = cov + t * w.D;
        const wide s = scale[t];
        wide dot = 0;
        for (uint32_t i = lane; i < w.D; i += 32) {
            dot += (wide)rt[i] * (wide)ct[i];
        }
        dot = warp_sum(dot);
        const wide mean = div_nearest(dot, (wide)w.D);
        for (uint32_t i = lane; i < w.D; i += 32) {
            const int64_t back = s == 0 ? 0 : fit64(div_nearest(((wide)ct[i] - rel(mean * (wide)rt[i], 2 * FACE_BITS)) << FACE_BITS, s), w.status);
            dst[t * w.D + i] = base ? fit64((wide)base[t * w.D + i] + (wide)back, w.status) : back;
        }
    }
}

// The pair contact's return: `da = release(dc ⊙ b, 16)`, `db = release(dc ⊙ a, 16)`.
extern "C" __global__ void field_pair_back(FieldWords w, const int64_t *dc, int64_t *da, int64_t *db) {
    const uint64_t cells = (uint64_t)w.T * w.f;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        da[c] = fit64(rel((wide)dc[c] * (wide)w.pb[c], FACE_BITS), w.status);
        db[c] = fit64(rel((wide)dc[c] * (wide)w.pa[c], FACE_BITS), w.status);
    }
}

// The wrapping sum of two drives' returns (the host's `i64` addition).
extern "C" __global__ void field_add(FieldWords w, const int64_t *p, int64_t *q, uint64_t cells) {
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        q[c] = (int64_t)((uint64_t)p[c] + (uint64_t)q[c]);
    }
}

// `δỹ = U ⊙ δy` by head, then each receiver's covector over its row's mass carried 2^(−30) finer,
// `w = div_nearest(δỹ 2^70, mass)`: both `[h][t][2n]`.
extern "C" __global__ void field_current_back(FieldWords w, const int64_t *dy, int64_t *dyh, int64_t *wr) {
    const uint64_t cells = (uint64_t)w.H * w.T * w.n;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t li = c % w.n;
        const uint64_t t = (c / w.n) % w.T;
        const uint32_t h = c / ((uint64_t)w.n * w.T);
        const uint32_t m = h * w.n + li;
        wide ur, ui;
        frame_of(w, w.site_pos[t], h, li, &ur, &ui);
        const wide gr = dy[t * w.M2 + m], gi = dy[t * w.M2 + w.M + m];
        const uint64_t at = ((uint64_t)h * w.T + t) * w.span;
        const int64_t re = fit64(rel(ur * gr - ui * gi, MOVE_BITS), w.status);
        const int64_t im = fit64(rel(ui * gr + ur * gi, MOVE_BITS), w.status);
        dyh[at + li] = re;
        dyh[at + w.n + li] = im;
        const wide mass = w.mass[(uint64_t)h * w.T + t];
        for (uint32_t part = 0; part < 2; part++) {
            const int64_t v = part == 0 ? re : im;
            // The host's `checked_mul` by `2^70`: in range exactly when `−2^57 ≤ v < 2^57`.
            if (v >= ((int64_t)1 << (127 - CARRIED_BITS)) || v < -((int64_t)1 << (127 - CARRIED_BITS))) {
                atomicOr(w.status, REFUSED_SHIFT);
                continue;
            }
            wr[at + part * w.n + li] = fit64(div_nearest((wide)v << CARRIED_BITS, mass), w.status);
        }
    }
}

// `v · 2^(−β)` (the host's `gained`): released `β` bits where the gain shifts down, `−β` exact
// doublings where it amplifies, refused past the carrier.
__device__ __forceinline__ wide gained(wide v, int32_t beta, uint32_t *st) {
    if (beta >= 0) {
        return rel(v, (uint32_t)beta);
    }
    // The host's `checked_mul` by `2^(−β)`: in range exactly when `−2^(127+β) ≤ v < 2^(127+β)`.
    const wide limit = (wide)((uwide)1 << (127 + beta));
    if (v >= limit || v < -limit) {
        atomicOr(st, REFUSED_CARRIER);
        return 0;
    }
    return v * ((wide)1 << -beta);
}

// The contact's return over one head's rows, one warp a receiving site `i` (`Field::returned`): over
// its support, `δp_ij = ⟨δỹ_i, ṽ_j⟩`, the mean `μ_i = div_nearest(Σ_j e_ij δp_ij, mass_i)`,
// `δs_ij = gained(release(ln2 div_nearest(e_ij (δp_ij − μ_i), mass_i), 30) + closure, β)` held at the
// region block's dense address for the columns' return, and the word's row return
// `release(Σ_(j∈S_i) δs_ij w̃_j, 32)` written to its framed chart slot.
//
// [agent-inferred, November 1] Two passes over the support: the first holds `δp_ij` and sums the mean
// and the closure's holders; the second turns each into `δs_ij` (the mass read once as a divisor,
// `divide_by`) in chunks of 32 into the warp's shared chunk, whose sum over the word is read with the
// lanes over the span's entries.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_rows(FieldWords w, uint32_t h, uint32_t closes, const int64_t *dyh, wide *ds, int64_t *dq) {
    __shared__ wide dss[CONTACT_ROWS][32];
    __shared__ uint32_t js[CONTACT_ROWS][32];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span;
    const uint32_t classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const uint32_t entry = lane % S, part = lane / S;
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    const bool still = still_head(w, h);
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t r = w.site_region[g];
        const uint32_t i = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[(uint64_t)h * w.T + g];
        const uint32_t K = support_len(off, c, known_site(w, g));
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        wide *dsr = ds + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *dyi = dyh + ((uint64_t)h * w.T + g) * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const uint64_t mass = w.mass[(uint64_t)h * w.T + g];
        // The closure (§19), over the support: on a still head at a closing tick, an unresolved site's
        // row is also compared with where its class stands among the sites it meets:
        // `δz_ij += p_ij − [j holds it] e_ij/Σ_(k∈S_i holds it) e_ik`, over its ring set's heads
        // (`closes` is their count, zero where the head does not close). A carried site holds nothing.
        const bool open = closes != 0 && w.unresolved[g] != 0;
        const uint32_t cls = w.classes[g];
        const auto holds = [&](uint32_t j) { return w.unresolved[first + j] == 0 && w.mix_off[first + j] == w.mix_off[first + j + 1] && w.classes[first + j] == cls; };
        wide weighted = 0;
        wide held = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, c, i, sites, k);
            if (j == UINT32_MAX) {
                continue;
            }
            const int64_t *vj = values + (uint64_t)j * S;
            const uint32_t gap = j > i ? j - i : i - j;
            wide dp = 0;
            for (uint32_t x = 0; x < S; x++) {
                dp += (wide)dyi[x] * carried(w, h, x % w.n, gap, vj[x]);
            }
            dsr[j] = dp;
            weighted += (wide)e[j] * dp;
            held += (open && holds(j)) ? (wide)e[j] : 0;
        }
        __syncwarp();
        const wide mean = div_nearest(warp_sum(weighted), (wide)mass);
        // The holders' mass is a part of the row's, so it is a 64-bit divisor as the row's is.
        const wide holders = warp_sum(held);
        const Divisor by = divisor_of(mass);
        const uint64_t copies = closes != 0 ? closes : 1;
        const Divisor cb = divisor_of((uint64_t)fit64((wide)mass * (wide)copies, w.status));
        const Divisor hb = divisor_of(holders > 0 ? (uint64_t)fit64(holders * (wide)copies, w.status) : 1);
        wide sum = 0;
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, c, i, sites, k) : UINT32_MAX;
            wide dz = 0;
            if (j != UINT32_MAX) {
                dz = rel(ln2 * div_nearest_by((wide)e[j] * (dsr[j] - mean), by), MOVE_BITS);
                if (holders > 0) {
                    const wide at = (wide)e[j] << CONTACT_BITS;
                    dz += div_nearest_by(at, cb) - (holds(j) ? div_nearest_by(at, hb) : 0);
                }
                dz = gained(dz, w.beta, w.status);
                if ((dz < 0 ? -dz : dz) >> w.dsbits != 0) {
                    atomicOr(w.status, REFUSED_CARRIER);
                }
                dsr[j] = dz;
            }
            dss[warp][lane] = dz;
            js[warp][lane] = j;
            __syncwarp();
            if (part < parts) {
                for (uint32_t jj = part; jj < 32; jj += parts) {
                    const uint32_t j = js[warp][jj];
                    if (j != UINT32_MAX) {
                        const wide term = dss[warp][jj] * (wide)words[(uint64_t)j * S + entry];
                        sum += still ? term : term * decay_of(w, h, entry % w.n, j > i ? j - i : i - j);
                    }
                }
            }
            __syncwarp();
        }
        sum = parts_sum(part < parts ? sum : 0, S, parts);
        if (lane < S) {
            const uint32_t m = h * w.n + lane % w.n;
            dq[g * w.M2 + (lane < w.n ? m : w.M + m)] = fit64(rel(sum, CONTACT_BACK + (still ? 0 : MOVE_BITS)), w.status);
        }
    }
}

// The word's column return and the values' over one head (`Field::returned`), one warp a source site
// `j` over its support (the support is symmetric, so the receivers that meet `j` are its own support):
// `δw̃_j += release(Σ_i δs_ij w̃_i, 32)` added to the rows' return in its framed chart slot, and
// `δṽ_j = release(Σ_i e_ij w_i, 70)`, the lanes over the span's entries (a lane an entry and a part of
// the support), `e_ij` and `δs_ij` read at the region block's dense address `[i][j]`.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_columns(FieldWords w, uint32_t h, const int64_t *wr, const wide *ds, int64_t *dq, int64_t *dv) {
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t S = w.span;
    const uint32_t classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const uint32_t entry = lane % S, part = lane / S;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t r = w.site_region[g];
        const uint32_t j = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[(uint64_t)h * w.T + g];
        const uint32_t K = support_len(off, c, known_site(w, g));
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + j;
        const wide *dsc = ds + w.region_eoff[r] + j;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *wh = wr + ((uint64_t)h * w.T + first) * S;
        wide sk = 0, sv = 0;
        const bool still = still_head(w, h);
        if (part < parts) {
            for (uint32_t k = part; k < K; k += parts) {
                const uint32_t i = support_at(members, off, c, j, sites, k);
                if (i == UINT32_MAX) {
                    continue;
                }
                const uint64_t at = (uint64_t)i * sites;
                const uint32_t gap = j > i ? j - i : i - j;
                const wide term = dsc[at] * (wide)words[(uint64_t)i * S + entry];
                sk += still ? term : term * decay_of(w, h, entry % w.n, gap);
                sv += (wide)e[at] * carried(w, h, entry % w.n, gap, wh[(uint64_t)i * S + entry]);
            }
        }
        sk = parts_sum(part < parts ? sk : 0, S, parts);
        sv = parts_sum(part < parts ? sv : 0, S, parts);
        if (lane < S) {
            const uint32_t m = h * w.n + lane % w.n;
            const uint64_t slot = g * w.M2 + (lane < w.n ? m : w.M + m);
            dq[slot] = fit64((wide)dq[slot] + rel(sk, CONTACT_BACK + (still ? 0 : MOVE_BITS)), w.status);
            dv[slot] = fit64(rel(sv, CARRIED_BITS), w.status);
        }
    }
}

// Undo the frame on a chart's covector: `δq = conj(U) ⊙ δq̃` (`[t][2M]`).
extern "C" __global__ void field_unframe(FieldWords w, int64_t *chart) {
    const uint64_t cells = (uint64_t)w.T * w.M;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.M;
        const uint32_t m = c % w.M;
        wide ur, ui;
        frame_of(w, w.site_pos[t], m / w.n, m % w.n, &ur, &ui);
        const wide gr = chart[t * w.M2 + m], gi = chart[t * w.M2 + w.M + m];
        chart[t * w.M2 + m] = fit64(rel(ur * gr + ui * gi, MOVE_BITS), w.status);
        chart[t * w.M2 + w.M + m] = fit64(rel(ur * gi - ui * gr, MOVE_BITS), w.status);
    }
}

// A family's covector `g[o][i] += Σ_t y_t[o] x_t[i]` over the batch's sites (`outer_sum`); with no
// `x`, the bias `g[o] += Σ_t y_t[o]`. An integer sum: the host's bits in any order.
//
// [agent-inferred, November 1] One thread an entry and a tile of `OUTER_TILE` sites, its partial
// added to the entry by the ring's atomic step (`add_wide`). (The first realization gave one thread
// an entry and every site of the batch, so a bias of 32 entries was summed by 32 threads over
// thousands of sites each.)
#define OUTER_TILE 64
template <typename X>
__device__ void outer(const FieldWords &w, wide *g, uint64_t at, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const X *x, uint64_t x_stride, uint32_t only_unresolved) {
    const uint64_t entries = (uint64_t)rows * (x ? cols : 1);
    const uint64_t tiles = ((uint64_t)w.T + OUTER_TILE - 1) / OUTER_TILE;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < entries * tiles; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t entry = c % entries, tile = c / entries;
        const uint64_t o = x ? entry / cols : entry, i = x ? entry % cols : 0;
        const uint64_t from = tile * OUTER_TILE;
        const uint64_t to = from + OUTER_TILE < w.T ? from + OUTER_TILE : w.T;
        wide sum = 0;
        for (uint64_t t = from; t < to; t++) {
            if (only_unresolved && !w.unresolved[t]) {
                continue;
            }
            const wide yv = y[t * y_stride + o];
            sum += x ? yv * (wide)x[t * x_stride + i] : yv;
        }
        if (sum != 0) {
            add_wide(g + at + entry, sum);
        }
    }
}

extern "C" __global__ void field_outer_x32(FieldWords w, wide *g, uint64_t at, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int32_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer<int32_t>(w, g, at, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

extern "C" __global__ void field_outer_x64(FieldWords w, wide *g, uint64_t at, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int64_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer<int64_t>(w, g, at, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

// The host's refusal of an outer sum, region by region: `Σ_t max|y_t| max|x_t| ≥ 2^126` refused
// (`outer_sum`'s bound, read per region as the host reads each region's sum). One block a region.
template <typename X>
__device__ void outer_bound(const FieldWords &w, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const X *x, uint64_t x_stride, uint32_t only_unresolved) {
    __shared__ uwide part[32];
    const uint32_t r = blockIdx.x;
    if (r >= w.R) {
        return;
    }
    uwide bound = 0;
    bool over = false;
    for (uint64_t t = w.region_off[r] + threadIdx.x; t < w.region_off[r + 1]; t += blockDim.x) {
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        uint64_t ym = 0, xm = 0;
        for (uint32_t o = 0; o < rows; o++) {
            const uint64_t m = mag64(y[t * y_stride + o]);
            ym = m > ym ? m : ym;
        }
        for (uint32_t i = 0; i < cols; i++) {
            const uint64_t m = mag64((int64_t)x[t * x_stride + i]);
            xm = m > xm ? m : xm;
        }
        const uwide term = (uwide)ym * (uwide)xm;
        over = over || bound + term < bound || bound + term >= ((uwide)1 << 126);
        bound += term;
    }
    // Each thread's partial is below 2^126 unless it is over; the block's sum of 32 such is read in
    // the ring and compared, any partial over refusing.
    const uint32_t lane = threadIdx.x & 31, warp = threadIdx.x >> 5;
    uwide v = bound;
    uint32_t flag = over ? 1u : 0u;
    for (int o = 16; o > 0; o >>= 1) {
        const uwide u = shfl_wide(v, o);
        flag |= __shfl_xor_sync(0xffffffffu, flag, o);
        flag |= (v + u < v) ? 1u : 0u;
        v += u;
    }
    if (lane == 0) {
        part[warp] = v;
        if (flag || v >= ((uwide)1 << 126)) {
            atomicOr(w.status, REFUSED_CARRIER);
        }
    }
    __syncthreads();
    if (threadIdx.x == 0) {
        uwide s = 0;
        for (uint32_t k = 0; k < (blockDim.x >> 5); k++) {
            if (s + part[k] < s || s + part[k] >= ((uwide)1 << 126)) {
                atomicOr(w.status, REFUSED_CARRIER);
            }
            s += part[k];
        }
    }
}

extern "C" __global__ void field_outer_bound_x32(FieldWords w, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int32_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer_bound<int32_t>(w, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

extern "C" __global__ void field_outer_bound_x64(FieldWords w, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int64_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer_bound<int64_t>(w, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

// An encoding's covector: each row's `Σ_t release(w_t dx_t, 16)` over the sites that opened on it,
// `w_t` the site's share of that row (`2^16` where it opened on the row itself, so the term is `dx_t`
// exactly; a carried site's shares of its mixture, `Field::opening_return`); `E`'s by their own class,
// `E₋`'s by the site before them, `E₊`'s by the site after; one launch each, `base` the encoding's
// offset), the entries sorted by row (`rows_sites`, `rows_shares`) and cut into segments of at most
// `OUTER_TILE` of one row (`segments`, each its row, first and end in `rows_sites`), one thread a
// segment and a column, its partial added by the ring's atomic step.
extern "C" __global__ void field_encoding(FieldWords w, wide *g, const int64_t *dx, const uint32_t *rows_sites, const uint32_t *rows_shares, const uint32_t *segments, uint32_t count, uint64_t base) {
    const uint64_t cells = (uint64_t)count * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t segment = c / w.D, i = c % w.D;
        const uint32_t row = segments[3 * segment];
        wide sum = 0;
        for (uint32_t k = segments[3 * segment + 1]; k < segments[3 * segment + 2]; k++) {
            sum += rel((wide)rows_shares[k] * (wide)dx[(uint64_t)rows_sites[k] * w.D + i], FACE_BITS);
        }
        if (sum != 0) {
            add_wide(g + base + (uint64_t)row * w.D + i, sum);
        }
    }
}
