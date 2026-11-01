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
// host's bits whatever the order. A contact row is read in three passes over its keys (the peak, the
// weights and their mass, the current's numerators): an online rescaling would round each partial sum
// at a peak that later moves, and the bits would follow the tile order.

#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

#define FACE_BITS 16
#define MATERIAL_BITS 24
#define MOVE_BITS 30
#define COVECTOR_BITS 24
#define UNIT_BITS 62
#define WEIGHT_BITS_FROM 22
#define CARRIED_BITS 70
#define CONTACT_BACK 32

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
// `div_nearest`, `fit64`, `fit32`, `u128::isqrt`, `Exponential::below_one`), and each image's parity
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

// `2^(x / 2^X)` for `x ≤ 0` on `2^(−62)`, at least one grain (`Exponential::below_one`).
__device__ uint64_t below_one(wide x, const uint64_t *roots, uint32_t digits) {
    const wide m = -x;
    const wide whole = m >> digits;
    const wide frac = m & (((wide)1 << digits) - 1);
    wide shift;
    wide rest;
    if (frac == 0) {
        shift = whole;
        rest = 0;
    } else {
        shift = whole + 1;
        rest = ((wide)1 << digits) - frac;
    }
    uint64_t value = (uint64_t)1 << UNIT_BITS;
    for (uint32_t i = 0; i < digits; i++) {
        if (rest & ((wide)1 << (digits - 1 - i))) {
            const uint64_t lo = value * roots[i];
            const uint64_t hi = __umul64hi(value, roots[i]);
            value = (hi << (64 - UNIT_BITS)) | (lo >> UNIT_BITS);
        }
    }
    const uint64_t shifted = shift >= 64 ? 0 : value >> (uint32_t)shift;
    return shifted == 0 ? 1 : shifted;
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
    uint64_t enc, q, q_bias, k, k_bias, v, v_bias, out, out_bias, a, a_bias, b, b_bias, w, w_bias, read, read_bias;
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
};

__device__ __forceinline__ void frame_of(const FieldWords &w, uint32_t t, uint32_t h, uint32_t l, wide *ur, wide *ui) {
    if (l < w.still) {
        *ur = (wide)1 << MOVE_BITS;
        *ui = 0;
        return;
    }
    const uint32_t slot = (l - w.still) * w.frames + h % w.frames;
    const uint64_t at = w.ring_off[slot] + t % w.ring_n[slot];
    *ur = w.phasor[2 * at];
    *ui = w.phasor[2 * at + 1];
}

// A site's opening face `x⁰`: its class's row of the encoding, or the unresolved row.
extern "C" __global__ void field_open(FieldWords w) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        const uint64_t row = w.unresolved[t] ? w.A : w.classes[t];
        w.x[c] = w.theta[w.enc + row * w.D + i];
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
// imaginary, each product released to `2^(−16)`.
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
        const int64_t *qkv = w.qkv + t * 3 * w.M2;
        const wide qr = qkv[m], qi = qkv[w.M + m];
        const wide kr = qkv[w.M2 + m], ki = qkv[w.M2 + w.M + m];
        const wide vr = qkv[2 * w.M2 + m], vi = qkv[2 * w.M2 + w.M + m];
        w.qf[at + li] = fit64(rel(ur * qr - ui * qi, MOVE_BITS), w.status);
        w.qf[at + w.n + li] = fit64(rel(ui * qr + ur * qi, MOVE_BITS), w.status);
        w.kf[at + li] = fit64(rel(ur * kr - ui * ki, MOVE_BITS), w.status);
        w.kf[at + w.n + li] = fit64(rel(ui * kr + ur * ki, MOVE_BITS), w.status);
        w.vf[at + li] = fit64(rel(ur * vr - ui * vi, MOVE_BITS), w.status);
        w.vf[at + w.n + li] = fit64(rel(ui * vr + ur * vi, MOVE_BITS), w.status);
    }
}

// The contact, the weights and the current of one row (a head and a receiving site), one warp a row,
// its lanes over the region's sites, in three passes: the scores and their peak (each score held in
// its weight's slot), the weights `release(2^(z − peak), 22)` and their mass, then the current's
// numerators `Σ_j e_ij ṽ_j`, divided once by the mass and returned to the receiver's frame.
#define MODE_CHUNK 8
extern "C" __global__ void field_contact(FieldWords w) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t row = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; row < rows; row += warps) {
        const uint32_t h = row / w.T;
        const uint64_t g = row % w.T;
        const uint32_t r = w.site_region[g];
        const uint32_t i = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - first;
        uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *qi = w.qf + ((uint64_t)h * w.T + g) * w.span;
        const int64_t *keys = w.kf + ((uint64_t)h * w.T + first) * w.span;
        int64_t peak = INT64_MIN;
        for (uint32_t j = lane; j < sites; j += 32) {
            const int64_t *kj = keys + (uint64_t)j * w.span;
            wide s = 0;
            for (uint32_t c = 0; c < w.span; c++) {
                s += (wide)qi[c] * (wide)kj[c];
            }
            const int64_t z = fit64(rel(s, FACE_BITS + w.beta), w.status);
            e[j] = (uint64_t)z;
            peak = z > peak ? z : peak;
        }
        peak = warp_max_signed(peak);
        // [agent-inferred, November 1] The weights, their mass and the current's numerators for the
        // first `MODE_CHUNK` modes in one pass (the numerators need the mass only at their division),
        // further modes a chunk at a time from the held weights. (The first realization read every
        // weight back once for each mode.)
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * w.span;
        uint64_t mass = 0;
        for (uint32_t l0 = 0; l0 == 0 || l0 < w.n; l0 += MODE_CHUNK) {
            wide sr[MODE_CHUNK], si[MODE_CHUNK];
#pragma unroll
            for (uint32_t k = 0; k < MODE_CHUNK; k++) {
                sr[k] = 0;
                si[k] = 0;
            }
            for (uint32_t j = lane; j < sites; j += 32) {
                uint64_t ej;
                if (l0 == 0) {
                    const int64_t z = (int64_t)e[j];
                    ej = (uint64_t)rel((wide)below_one((wide)z - (wide)peak, w.roots, w.digits), WEIGHT_BITS_FROM);
                    e[j] = ej;
                    mass += ej;
                } else {
                    ej = e[j];
                }
                const int64_t *vj = values + (uint64_t)j * w.span;
#pragma unroll
                for (uint32_t k = 0; k < MODE_CHUNK; k++) {
                    if (l0 + k < w.n) {
                        sr[k] += (wide)ej * (wide)vj[l0 + k];
                        si[k] += (wide)ej * (wide)vj[w.n + l0 + k];
                    }
                }
            }
            if (l0 == 0) {
                mass = warp_sum_u64(mass);
                if (lane == 0) {
                    w.mass[(uint64_t)h * w.T + g] = mass;
                }
            }
#pragma unroll
            for (uint32_t k = 0; k < MODE_CHUNK; k++) {
                if (l0 + k < w.n) {
                    const wide nr = warp_sum(sr[k]);
                    const wide ni = warp_sum(si[k]);
                    if (lane == 0) {
                        const uint32_t li = l0 + k;
                        const wide yr = fit64(div_nearest(nr, (wide)mass), w.status);
                        const wide yi = fit64(div_nearest(ni, (wide)mass), w.status);
                        wide ur, ui;
                        frame_of(w, i, h, li, &ur, &ui);
                        const uint32_t m = h * w.n + li;
                        w.y[g * w.M2 + m] = fit64(rel(ur * yr + ui * yi, MOVE_BITS), w.status);
                        w.y[g * w.M2 + w.M + m] = fit64(rel(ur * yi - ui * yr, MOVE_BITS), w.status);
                    }
                }
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
            const uint64_t m = below_one((wide)zt[c] - (wide)peak, w.roots, w.digits);
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
extern "C" __global__ void field_contact_rows(FieldWords w, uint32_t h, const int64_t *dyh, wide *ds, int64_t *dq) {
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
        wide weighted = 0;
        for (uint32_t j = lane; j < sites; j += 32) {
            const int64_t *vj = values + (uint64_t)j * w.span;
            wide dp = 0;
            for (uint32_t c = 0; c < w.span; c++) {
                dp += (wide)dyi[c] * (wide)vj[c];
            }
            dsr[j] = dp;
            weighted += (wide)e[j] * dp;
        }
        const wide mean = div_nearest(warp_sum(weighted), (wide)mass);
        const Divisor by = divisor_of(mass);
        for (uint32_t c0 = 0; c0 == 0 || c0 < w.span; c0 += ROW_CHUNK) {
            wide sum[ROW_CHUNK];
#pragma unroll
            for (uint32_t k = 0; k < ROW_CHUNK; k++) {
                sum[k] = 0;
            }
            for (uint32_t j = lane; j < sites; j += 32) {
                wide dz;
                if (c0 == 0) {
                    dz = rel(rel(ln2 * div_nearest_by((wide)e[j] * (dsr[j] - mean), by), MOVE_BITS), w.beta);
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

// The encoding's covector: each row's `Σ_t dx_t` over the sites that opened on it, the sites sorted by
// row (`rows_sites`) and cut into segments of at most `OUTER_TILE` sites of one row (`segments`, each
// its row, first and end in `rows_sites`), one thread a segment and a column, its partial added by
// the ring's atomic step. (The first realization gave the unresolved row's column one thread over
// every unresolved site.)
extern "C" __global__ void field_encoding(FieldWords w, wide *g, const int64_t *dx, const uint32_t *rows_sites, const uint32_t *segments, uint32_t count) {
    const uint64_t cells = (uint64_t)count * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t segment = c / w.D, i = c % w.D;
        const uint32_t row = segments[3 * segment];
        wide sum = 0;
        for (uint32_t k = segments[3 * segment + 1]; k < segments[3 * segment + 2]; k++) {
            sum += dx[(uint64_t)rows_sites[k] * w.D + i];
        }
        if (sum != 0) {
            add_wide(g + w.enc + (uint64_t)row * w.D + i, sum);
        }
    }
}
