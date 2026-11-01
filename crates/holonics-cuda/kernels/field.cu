// The field's card realization (`holonics::hnn::tower::field`, record
// `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`,
// §7): one constitution iterated over every site of every region of a batch at once, and its exact
// reverse, bit for bit the host's `Field::pass` and `Field::reverse`.
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
    uint32_t D, H, n, still, f, A, frames, beta;
    uint32_t M, M2, span, digits;
    uint32_t T, R;
    uint64_t E;
    // `ln 2` on `2^(−30)`, the weights' return reads it (two words of a signed 128-bit value).
    uint64_t ln2_lo, ln2_hi;
    const int32_t *theta;
    uint64_t enc, enc_before, enc_after, q, q_bias, k, k_bias, v, v_bias, out, out_bias, a, a_bias, b, b_bias, w, w_bias, read, read_bias;
    uint64_t rq, rk, rv, rout, ra, rb, rw, rread;
    const int64_t *phasor;
    const uint64_t *ring_off;
    const uint64_t *ring_n;
    const uint64_t *roots;
    const uint32_t *site_region;
    const uint32_t *site_pos;
    const uint32_t *region_off;
    const uint64_t *region_eoff;
    const uint32_t *classes;
    const uint8_t *unresolved;
    uint32_t *status;
    // The tick's carriers the frame, the contact and the pair contact read and write (the charts'
    // reads and scales are passed to their own launches).
    int64_t *x;
    int64_t *qkv;
    int64_t *qf, *kf, *vf;
    uint64_t *e;
    uint64_t *mass;
    int64_t *y;
    int64_t *pa, *pb, *pc;
    // The tick's magnitudes (the binary lengths of the largest framed probe, key and value, written
    // by the frame) and the exponential's resident face.
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

// A site's opening face `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))`: its row of the encoding with its
// strand neighbours' rows of theirs, a neighbour only within the site's own region (a site at its
// region's first place has none before it; the next site is the region's own when its place is not
// the first).
extern "C" __global__ void field_open(FieldWords w) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        int64_t x = w.theta[w.enc + row_of(w, t) * w.D + i];
        if (w.site_pos[t] > 0) {
            x += w.theta[w.enc_before + row_of(w, t - 1) * w.D + i];
        }
        if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
            x += w.theta[w.enc_after + row_of(w, t + 1) * w.D + i];
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

// The frame, by head: `q̃ = U ⊙ q` and so for the keys and values, `[h][t][2n]` real parts then
// imaginary, each product released to `2^(−16)`; the binary length of the largest framed value is
// raised into `bits[2]` (zeroed before the launch), a carrier's width the contact reads (the probe's
// and the key's are raised by `field_unit`, which reads them at unit power).
extern "C" __global__ void field_frame(FieldWords w) {
    const uint64_t cells = (uint64_t)w.H * w.T * w.n;
    uint32_t vb = 0;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t li = c % w.n;
        const uint64_t t = (c / w.n) % w.T;
        const uint32_t h = c / ((uint64_t)w.n * w.T);
        const uint32_t m = h * w.n + li;
        wide ur, ui;
        frame_of(w, w.site_pos[t], h, li, &ur, &ui);
        const uint64_t at = ((uint64_t)h * w.T + t) * w.span;
        const int64_t *qkv = w.qkv + t * 3 * w.M2;
        const wide qr = qkv[m], qi = qkv[w.M + m];
        const wide kr = qkv[w.M2 + m], ki = qkv[w.M2 + w.M + m];
        const wide vr = qkv[2 * w.M2 + m], vi = qkv[2 * w.M2 + w.M + m];
        const int64_t q0 = fit64(rel(ur * qr - ui * qi, MOVE_BITS), w.status), q1 = fit64(rel(ui * qr + ur * qi, MOVE_BITS), w.status);
        const int64_t k0 = fit64(rel(ur * kr - ui * ki, MOVE_BITS), w.status), k1 = fit64(rel(ui * kr + ur * ki, MOVE_BITS), w.status);
        const int64_t v0 = fit64(rel(ur * vr - ui * vi, MOVE_BITS), w.status), v1 = fit64(rel(ui * vr + ur * vi, MOVE_BITS), w.status);
        w.qf[at + li] = q0;
        w.qf[at + w.n + li] = q1;
        w.kf[at + li] = k0;
        w.kf[at + w.n + li] = k1;
        w.vf[at + li] = v0;
        w.vf[at + w.n + li] = v1;
        vb = max(vb, bit_length(mag64(v0) | mag64(v1)));
    }
    vb = (uint32_t)warp_max_u64(vb);
    if ((threadIdx.x & 31) == 0) {
        atomicMax(&w.bits[2], vb);
    }
}

// [agent-inferred, November 1] **The contact pairs words at unit power** (`Field::tick`): each head's
// framed probe and key read in place as a ratio to its own power over the head's `2n` reals
// (`ratio_to_power`, on `2^(−16)`), their powers kept for the return; one warp a head and a site
// (`[h][t]`). The binary lengths of the largest unit probe and key are raised into `bits[0]`,
// `bits[1]`.
extern "C" __global__ void field_unit(FieldWords w, wide *qscale, wide *kscale) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    uint32_t qb = 0, kb = 0;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        for (uint32_t part = 0; part < 2; part++) {
            int64_t *c = (part == 0 ? w.qf : w.kf) + hs * w.span;
            wide power = 0;
            for (uint32_t i = lane; i < w.span; i += 32) {
                power += (wide)c[i] * (wide)c[i];
            }
            power = warp_sum(power);
            const wide s = (wide)isqrt128((uwide)(power / (wide)w.span));
            uint32_t b = 0;
            for (uint32_t i = lane; i < w.span; i += 32) {
                const int64_t r = s == 0 ? 0 : (int64_t)fit32(div_nearest((wide)c[i] << FACE_BITS, s), w.status);
                c[i] = r;
                b = max(b, bit_length(mag64(r)));
            }
            if (part == 0) {
                qb = max(qb, b);
            } else {
                kb = max(kb, b);
            }
            if (lane == 0) {
                (part == 0 ? qscale : kscale)[hs] = s;
            }
        }
    }
    qb = (uint32_t)warp_max_u64(qb);
    kb = (uint32_t)warp_max_u64(kb);
    if (lane == 0) {
        atomicMax(&w.bits[0], qb);
        atomicMax(&w.bits[1], kb);
    }
}

// The return through the probe's and the key's unit power (`ratio_adjoint`), in place on their
// framed charts' covectors `[t][2M]` (head `h`'s slots `h n + l` and `M + h n + l`):
// `δq̃ = (δq̂ − q̂ ⟨q̂, δq̂⟩/2n) / ‖q̃‖_rms`; one warp a head and a site.
extern "C" __global__ void field_unit_back(FieldWords w, const wide *qscale, const wide *kscale, int64_t *dq, int64_t *dk) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        const uint32_t h = hs / w.T;
        const uint64_t t = hs % w.T;
        for (uint32_t part = 0; part < 2; part++) {
            const int64_t *rt = (part == 0 ? w.qf : w.kf) + hs * w.span;
            int64_t *chart = part == 0 ? dq : dk;
            const wide s = (part == 0 ? qscale : kscale)[hs];
            wide dot = 0;
            for (uint32_t c = lane; c < w.span; c += 32) {
                const uint64_t slot = t * w.M2 + (c < w.n ? h * w.n + c : w.M + h * w.n + c - w.n);
                dot += (wide)rt[c] * (wide)chart[slot];
            }
            dot = warp_sum(dot);
            const wide mean = div_nearest(dot, (wide)w.span);
            for (uint32_t c = lane; c < w.span; c += 32) {
                const uint64_t slot = t * w.M2 + (c < w.n ? h * w.n + c : w.M + h * w.n + c - w.n);
                chart[slot] = s == 0 ? 0 : fit64(div_nearest(((wide)chart[slot] - rel(mean * (wide)rt[c], 2 * FACE_BITS)) << FACE_BITS, s), w.status);
            }
        }
    }
}

// The contact, the weights and the current of the rows of one head, a block of `CONTACT_ROWS`
// consecutive receiving sites of one region (a warp a row), its keys and values read a tile of
// `KEY_TILE` sites at a time into the block's shared memory, so each key and value crosses from the
// card's memory once a block instead of once a row. Two passes over the keys: the scores and their
// peak; then each score again, its weight `release(2^(z − peak), 22)` through the exponential's
// resident face, the mass and the current's numerators `Σ_j e_ij ṽ_j`. The numerators are then
// divided once by the mass and returned to the receiver's frame. The weights are stored
// only when a return will read them (`store`). No site meets itself: the peak is read over the
// other sites and the receiver's own weight is zero (stored as zero, so the return reads it so).
//
// [agent-inferred, November 1] **The carriers' widths follow their terms** (the precision law: a
// carrier widens at a declared crossing). The frame wrote the binary lengths of the largest framed
// probe, key and value. Where a score's `2n` products and their sum fit 62 bits, the score is summed
// in 64 bits from 32-bit products; a weight `e ≤ 2^40` is read as `2^20 e_h + e_l` (`e_h ≤ 2^20`,
// `e_l < 2^20`), and where a row's `S` products of a part with a value fit 62 bits, the two parts'
// numerators are summed in 64 bits and joined as `2^20 N_h + N_l` on 128. Otherwise every sum is on
// 128 bits. The integers are the same either way, so the bits are the host's whatever the widths.
// In the second pass a lane holds one weight; the warp then sums a tile's `KEY_TILE` products for
// each of the span's entries, a lane an entry (two lanes an entry when the span is at most 16, each
// half of the tile), so a lane carries one numerator and not `2n`.
#define CONTACT_ROWS 8
#define KEY_TILE 32
#define TILE_PAD 33

// The score `release(Σ_c q_c k_jc, 16 + β)` of the warp's probe (`q`, shared) and the tile's key
// `lane` (`kt`, transposed).
__device__ __forceinline__ int64_t contact_score(const FieldWords &w, const int64_t *q, const int64_t *kt, uint32_t lane, bool narrow) {
    if (narrow) {
        int64_t s = 0;
        for (uint32_t c = 0; c < w.span; c++) {
            s += (int64_t)(int32_t)q[c] * (int64_t)(int32_t)kt[c * TILE_PAD + lane];
        }
        return fit64(rel((wide)s, FACE_BITS + w.beta), w.status);
    }
    wide s = 0;
    for (uint32_t c = 0; c < w.span; c++) {
        s += (wide)q[c] * (wide)kt[c * TILE_PAD + lane];
    }
    return fit64(rel(s, FACE_BITS + w.beta), w.status);
}

// The block's dynamic shared memory, in order (the host's `contact_shared` counts its octets): the
// tile's keys and values, transposed and padded (`[span][TILE_PAD]` each), the rows' probes
// (`[CONTACT_ROWS][span]`), the tile's weights (`[CONTACT_ROWS][KEY_TILE]`), the lanes' numerators
// (`[CONTACT_ROWS][32]`, 128 bits) and the rows' currents (`[CONTACT_ROWS][span]`, 128 bits).
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32, 4) field_contact(FieldWords w, const uint32_t *groups, uint32_t count, uint32_t store) {
    extern __shared__ __align__(16) unsigned char shared[];
    const uint32_t S = w.span;
    int64_t *kt = (int64_t *)shared;
    int64_t *vt = kt + S * TILE_PAD;
    int64_t *qs = vt + S * TILE_PAD;
    uint64_t *es = (uint64_t *)(qs + CONTACT_ROWS * S);
    wide *red = (wide *)(es + CONTACT_ROWS * KEY_TILE);
    wide *ys = red + CONTACT_ROWS * 32;
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const bool narrow_score = w.bits[0] <= 31 && w.bits[1] <= 31 && w.bits[0] + w.bits[1] + ceil_log2(S) <= 62;
    // A lane's entry of the span and its part of the tile.
    const uint32_t parts = S <= 16 ? 32 / S : 1;
    const uint32_t entry = lane % S, part = lane / S;
    const uint64_t blocks = (uint64_t)w.H * count;
    for (uint64_t u = blockIdx.x; u < blocks; u += gridDim.x) {
        const uint32_t h = u / count;
        const uint64_t g0 = groups[u % count];
        const uint32_t r = w.site_region[g0];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - first;
        const uint32_t i = w.site_pos[g0] + warp;
        const bool live = i < sites;
        const uint64_t g = first + i;
        const int64_t *keys = w.kf + ((uint64_t)h * w.T + first) * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const bool narrow_values = w.bits[2] <= 31 && WEIGHT_HALF + 1 + w.bits[2] + ceil_log2(sites) <= 62;
        __syncthreads();
        for (uint32_t c = lane; c < S; c += 32) {
            qs[warp * S + c] = live ? w.qf[((uint64_t)h * w.T + g) * S + c] : 0;
        }
        // The scores and their peak.
        int64_t peak = INT64_MIN;
        for (uint32_t j0 = 0; j0 < sites; j0 += KEY_TILE) {
            __syncthreads();
            for (uint32_t x = threadIdx.x; x < KEY_TILE * S; x += blockDim.x) {
                const uint32_t jj = x / S, c = x % S;
                kt[c * TILE_PAD + jj] = j0 + jj < sites ? keys[(uint64_t)(j0 + jj) * S + c] : 0;
            }
            __syncthreads();
            if (live && j0 + lane < sites && j0 + lane != i) {
                const int64_t z = contact_score(w, qs + warp * S, kt, lane, narrow_score);
                peak = z > peak ? z : peak;
            }
        }
        peak = warp_max_signed(peak);
        // The weights, their mass and the numerators.
        uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        uint64_t mass = 0;
        int64_t nh = 0, nl = 0;
        wide nw = 0;
        for (uint32_t j0 = 0; j0 < sites; j0 += KEY_TILE) {
            __syncthreads();
            for (uint32_t x = threadIdx.x; x < KEY_TILE * S; x += blockDim.x) {
                const uint32_t jj = x / S, c = x % S;
                const bool in = j0 + jj < sites;
                kt[c * TILE_PAD + jj] = in ? keys[(uint64_t)(j0 + jj) * S + c] : 0;
                vt[c * TILE_PAD + jj] = in ? values[(uint64_t)(j0 + jj) * S + c] : 0;
            }
            __syncthreads();
            uint64_t ej = 0;
            if (live && j0 + lane < sites) {
                if (j0 + lane != i) {
                    const int64_t z = contact_score(w, qs + warp * S, kt, lane, narrow_score);
                    ej = (uint64_t)rel((wide)below_one_face((wide)z - (wide)peak, w.face, w.digits), WEIGHT_BITS_FROM);
                    mass += ej;
                }
                if (store) {
                    erow[j0 + lane] = ej;
                }
            }
            es[warp * KEY_TILE + lane] = ej;
            __syncwarp();
            if (part < parts) {
                for (uint32_t jj = part; jj < KEY_TILE; jj += parts) {
                    const uint64_t e = es[warp * KEY_TILE + jj];
                    const int64_t v = vt[entry * TILE_PAD + jj];
                    if (narrow_values) {
                        nh += (int64_t)(int32_t)(e >> WEIGHT_HALF) * (int64_t)(int32_t)v;
                        nl += (int64_t)(int32_t)(e & (((uint64_t)1 << WEIGHT_HALF) - 1)) * (int64_t)(int32_t)v;
                    } else {
                        nw += (wide)e * (wide)v;
                    }
                }
            }
            __syncwarp();
        }
        mass = warp_sum_u64(mass);
        red[warp * 32 + lane] = part < parts ? (narrow_values ? ((wide)nh << WEIGHT_HALF) + (wide)nl : nw) : 0;
        __syncwarp();
        if (lane < S) {
            wide numerator = 0;
            for (uint32_t p = 0; p < parts; p++) {
                numerator += red[warp * 32 + p * S + lane];
            }
            ys[warp * S + lane] = live ? (wide)fit64(div_nearest(numerator, (wide)mass), w.status) : 0;
        }
        __syncwarp();
        if (live) {
            if (lane == 0) {
                w.mass[(uint64_t)h * w.T + g] = mass;
            }
            if (lane < w.n) {
                const wide yr = ys[warp * S + lane], yi = ys[warp * S + w.n + lane];
                wide ur, ui;
                frame_of(w, i, h, lane, &ur, &ui);
                const uint32_t m = h * w.n + lane;
                w.y[g * w.M2 + m] = fit64(rel(ur * yr + ui * yi, MOVE_BITS), w.status);
                w.y[g * w.M2 + w.M + m] = fit64(rel(ur * yi - ui * yr, MOVE_BITS), w.status);
            }
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
            if (mag64(v) >= ((uint64_t)1 << (127 - CARRIED_BITS))) {
                atomicOr(w.status, REFUSED_SHIFT);
                continue;
            }
            wr[at + part * w.n + li] = fit64(div_nearest((wide)v << CARRIED_BITS, mass), w.status);
        }
    }
}

// The contact's return over one head's rows, one warp a receiving site `i`: `δp_ij = ⟨δỹ_i, ṽ_j⟩`, the
// mean `μ_i = div_nearest(Σ_j e_ij δp_ij, mass_i)`, `δs_ij = release(release(ln2 div_nearest(e_ij
// (δp_ij − μ_i), mass_i), 30), β)` held for the keys' return, and the probe's return
// `δq̃_i = release(Σ_j δs_ij k̃_j, 32)` written to its framed chart slot.
//
// [agent-inferred, November 1] Two passes over the row's keys: the first holds `δp_ij` and sums the
// mean; the second turns each into `δs_ij` (the mass read once as a divisor, `divide_by`) and adds
// it into the probe's return for the span's first `ROW_CHUNK` entries at once, the rest read back
// from `δs` a chunk at a time. (The first realization divided a pair by a 128-bit software division
// and read `δs` once for every entry of the span.)
#define ROW_CHUNK 8
extern "C" __global__ void field_contact_rows(FieldWords w, uint32_t h, uint32_t closes, const int64_t *dyh, wide *ds, int64_t *dq) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += warps) {
        const uint32_t r = w.site_region[g];
        const uint32_t i = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - first;
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        wide *dsr = ds + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *dyi = dyh + ((uint64_t)h * w.T + g) * w.span;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * w.span;
        const int64_t *keys = w.kf + ((uint64_t)h * w.T + first) * w.span;
        const uint64_t mass = w.mass[(uint64_t)h * w.T + g];
        // The closure (§19): on a still head at a closing tick, an unresolved site's row is also
        // compared with where its class stands, the code of its class on the row's own copy face:
        // `δz_ij += p_ij − [j holds it] e_ij/Σ_(k holds it) e_ik`.
        const bool open = closes != 0 && w.unresolved[first + i] != 0;
        const uint32_t cls = w.classes[first + i];
        wide weighted = 0;
        wide held = 0;
        for (uint32_t j = lane; j < sites; j += 32) {
            const int64_t *vj = values + (uint64_t)j * w.span;
            wide dp = 0;
            for (uint32_t c = 0; c < w.span; c++) {
                dp += (wide)dyi[c] * (wide)vj[c];
            }
            dsr[j] = dp;
            weighted += (wide)e[j] * dp;
            held += (open && j != i && w.unresolved[first + j] == 0 && w.classes[first + j] == cls) ? (wide)e[j] : 0;
        }
        const wide mean = div_nearest(warp_sum(weighted), (wide)mass);
        // The holders' mass is a part of the row's, so it is a 64-bit divisor as the row's is.
        const wide holders = warp_sum(held);
        const Divisor by = divisor_of(mass);
        const Divisor hb = divisor_of(holders > 0 ? (uint64_t)holders : 1);
        for (uint32_t c0 = 0; c0 == 0 || c0 < w.span; c0 += ROW_CHUNK) {
            wide sum[ROW_CHUNK];
#pragma unroll
            for (uint32_t k = 0; k < ROW_CHUNK; k++) {
                sum[k] = 0;
            }
            for (uint32_t j = lane; j < sites; j += 32) {
                wide dz;
                if (c0 == 0) {
                    dz = rel(ln2 * div_nearest_by((wide)e[j] * (dsr[j] - mean), by), MOVE_BITS);
                    if (holders > 0) {
                        const bool holds = j != i && w.unresolved[first + j] == 0 && w.classes[first + j] == cls;
                        const wide at = (wide)e[j] << CONTACT_BITS;
                        dz += div_nearest_by(at, by) - (holds ? div_nearest_by(at, hb) : 0);
                    }
                    dz = rel(dz, w.beta);
                    dsr[j] = dz;
                } else {
                    dz = dsr[j];
                }
                const int64_t *kj = keys + (uint64_t)j * w.span + c0;
#pragma unroll
                for (uint32_t k = 0; k < ROW_CHUNK; k++) {
                    if (c0 + k < w.span) {
                        sum[k] += dz * (wide)kj[k];
                    }
                }
            }
#pragma unroll
            for (uint32_t k = 0; k < ROW_CHUNK; k++) {
                if (c0 + k < w.span) {
                    const wide s = warp_sum(sum[k]);
                    if (lane == 0) {
                        const uint32_t c = c0 + k;
                        const uint32_t m = h * w.n + c % w.n;
                        dq[g * w.M2 + (c < w.n ? m : w.M + m)] = fit64(rel(s, CONTACT_BACK), w.status);
                    }
                }
            }
        }
    }
}

// The keys' and values' return over one head's columns: `δk̃_j = release(Σ_i δs_ij q̃_i, 32)`,
// `δṽ_j = release(Σ_i e_ij w_i, 70)`.
//
// [agent-inferred, November 1] A block takes 32 consecutive source sites `j`, one a lane, and its
// warps split the receivers `i` between them; a lane reads `e_ij` and `δs_ij` along the row `i`, so a
// warp's reads are one run of the store (the first realization read a column with its lanes over
// `i`, 32 rows apart, once for every entry of the span). The warps' partial sums meet in shared
// memory, a chunk of the span at a time. Integer sums: the host's bits in any order.
#define COLUMN_CHUNK 4
#define COLUMN_SLICES 8
extern "C" __global__ void field_contact_columns(FieldWords w, uint32_t h, const int64_t *wr, const wide *ds, int64_t *dk, int64_t *dv) {
    __shared__ wide part[COLUMN_SLICES][2 * COLUMN_CHUNK][32];
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t slice = threadIdx.x >> 5;
    const uint32_t slices = blockDim.x >> 5;
    for (uint64_t base = (uint64_t)blockIdx.x * 32; base < w.T; base += (uint64_t)gridDim.x * 32) {
        const uint64_t g = base + lane;
        uint32_t sites = 0, j = 0;
        uint64_t first = 0, eoff = 0;
        if (g < w.T) {
            const uint32_t r = w.site_region[g];
            j = w.site_pos[g];
            first = w.region_off[r];
            sites = w.region_off[r + 1] - (uint32_t)first;
            eoff = w.region_eoff[r];
        }
        const uint64_t *e = w.e + (uint64_t)h * w.E + eoff + j;
        const wide *dsr = ds + eoff + j;
        const int64_t *probes = w.qf + ((uint64_t)h * w.T + first) * w.span;
        const int64_t *wh = wr + ((uint64_t)h * w.T + first) * w.span;
        for (uint32_t c0 = 0; c0 < w.span; c0 += COLUMN_CHUNK) {
            wide sk[COLUMN_CHUNK], sv[COLUMN_CHUNK];
#pragma unroll
            for (uint32_t k = 0; k < COLUMN_CHUNK; k++) {
                sk[k] = 0;
                sv[k] = 0;
            }
            for (uint32_t i = slice; i < sites; i += slices) {
                const uint64_t at = (uint64_t)i * sites;
                const wide d = dsr[at];
                const wide ew = (wide)e[at];
                const int64_t *pi = probes + (uint64_t)i * w.span + c0;
                const int64_t *wi = wh + (uint64_t)i * w.span + c0;
#pragma unroll
                for (uint32_t k = 0; k < COLUMN_CHUNK; k++) {
                    if (c0 + k < w.span) {
                        sk[k] += d * (wide)pi[k];
                        sv[k] += ew * (wide)wi[k];
                    }
                }
            }
#pragma unroll
            for (uint32_t k = 0; k < COLUMN_CHUNK; k++) {
                part[slice][k][lane] = sk[k];
                part[slice][COLUMN_CHUNK + k][lane] = sv[k];
            }
            __syncthreads();
            if (slice == 0 && g < w.T) {
#pragma unroll
                for (uint32_t k = 0; k < COLUMN_CHUNK; k++) {
                    if (c0 + k < w.span) {
                        uwide tk = 0, tv = 0;
                        for (uint32_t p = 0; p < slices; p++) {
                            tk += (uwide)part[p][k][lane];
                            tv += (uwide)part[p][COLUMN_CHUNK + k][lane];
                        }
                        const uint32_t c = c0 + k;
                        const uint32_t m = h * w.n + c % w.n;
                        const uint64_t slot = g * w.M2 + (c < w.n ? m : w.M + m);
                        dk[slot] = fit64(rel((wide)tk, CONTACT_BACK), w.status);
                        dv[slot] = fit64(rel((wide)tv, CARRIED_BITS), w.status);
                    }
                }
            }
            __syncthreads();
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

// An encoding's covector: each row's `Σ_t dx_t` over the sites that opened on it (`E`'s by their own
// class, `E₋`'s by the site before them, `E₊`'s by the site after; one launch each, `base` the
// encoding's offset), the sites sorted by row (`rows_sites`) and cut into segments of at most
// `OUTER_TILE` sites of one row (`segments`, each its row, first and end in `rows_sites`), one thread
// a segment and a column, its partial added by the ring's atomic step. (The first realization gave
// the unresolved row's column one thread over every unresolved site.)
extern "C" __global__ void field_encoding(FieldWords w, wide *g, const int64_t *dx, const uint32_t *rows_sites, const uint32_t *segments, uint32_t count, uint64_t base) {
    const uint64_t cells = (uint64_t)count * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t segment = c / w.D, i = c % w.D;
        const uint32_t row = segments[3 * segment];
        wide sum = 0;
        for (uint32_t k = segments[3 * segment + 1]; k < segments[3 * segment + 2]; k++) {
            sum += dx[(uint64_t)rows_sites[k] * w.D + i];
        }
        if (sum != 0) {
            add_wide(g + base + (uint64_t)row * w.D + i, sum);
        }
    }
}
