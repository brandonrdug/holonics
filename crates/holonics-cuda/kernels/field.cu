// The field's card realization (`holonics::hnn::tower::field`, records
// `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`,
// §7, and `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
// §6, §12 and §14): one constitution iterated over every site of every region of a batch at once, and
// its exact reverse, bit for bit the host's `Field::pass` and `Field::reverse`.
//
// [definition; agent-inferred, November 1] **The field disperses; only the plates radiate far.** Each
// head reads one word a site (the probe and the key at once); a site meets its near field
// (`0 < |i - j| < NEAR`) and the definite members of its resonance class (its word's shells; definite
// is known or locked, §14.1), each at the octave falloff `floor(log2 |i - j|)` bits, and a far source
// held by both ends (§14.2) at the product of their holds. Past the near field it also hears every
// definite source through its octave's crowd (§14.10). The classes are listed by one stable counting
// sort a head and region (`field_classes`), definite members first, and every contact kernel visits
// only the support. The shares and the contact's return keep the dense address `[i][j]` of the region's
// block, written and read only on the support, so a column's reads find `p_ij` without an index.
//
// [definition; agent-inferred, November 1] **The row is a series** (§14.11). A contact row is read in
// two passes over its terms (the least exponent `a_0`; then each term `face * mult * 2^(a - a_0)` summed
// whole into the mass and, times each value entry, into the numerators), in a carrier of
// `FieldDeclaration::row_bits()` bits (`LIMBS` limbs of 64, signed by two's complement), divided once
// by the mass (the exact long division, to the nearest numerator), and each term's share of the mass
// formed once by the same division on `2^-63`. Integer sums: the host's bits in any order, whatever
// the partition of the support over the warp's lanes.
//
// [definition; agent-inferred, November 1] The launch follows regions x sites x heads, never a padded
// window: a site is its global index in the batch (`site_region`, `site_pos`), a contact row is a head
// and a site, and a region's pairs are its own block of the share store (`region_eoff`). Every
// product's remainder below its grain is released to the nearest numerator (`rel`) and every sum is an
// integer sum, so a row read by 32 lanes, a covector summed over sites or a sum over regions gives the
// host's bits whatever the order.

#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

#define FACE_BITS 16
#define MATERIAL_BITS 24
#define MOVE_BITS 30
#define COVECTOR_BITS 24
#define UNIT_BITS 62
#define CARRIED_BITS 70
#define CONTACT_BACK 32
// The contact's covector grain, `δz` on `2^(−40)` (the host's `CONTACT_BITS`).
#define CONTACT_BITS 40
// A hold's face on `2^(−40)` (the host's `HOLD_BITS`, §14.2) and a term's share of its row's mass on
// `2^(−63)` (the host's `SHARE_BITS`, §14.11).
#define HOLD_BITS 40
#define SHARE_BITS 63
// The most crowds a receiver hears (two an octave, `2 (⌈log₂ reach⌉ − 1)` at most), kept in one warp.
#define MAX_CROWD_SLOTS 32

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
    // The series row's carrier in 64-bit limbs (`FieldDeclaration::row_bits()` rounded up) and the
    // crowds' slots a receiver keeps (`2 (levels − 1)` for the reach).
    uint32_t limbs, slots;
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
    // A definite site: known (resolved and carrying no mixture) or locked (a foil, §14.1).
    const uint8_t *definite;
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
    // The dense shares `p_ij` on `2^(−63)` (the support's entries only); while a row is read, its score.
    uint64_t *e;
    int64_t *y;
    int64_t *pa, *pb, *pc;
    // The tick's magnitude (the binary length of the largest unit word, `bits[0]`) and the
    // exponential's resident face.
    uint32_t *bits;
    const uint64_t *face;
    // The tick's holds `[h][t]` on `2^(−40)` and the mode that sets each (`hold`), each head's prefix
    // sums of the definite sites' unit words and values `[h][row][span]` and their counts `[h][row]`
    // (`row = region_off[r] + r + t`, a region's `S + 1` rows, §14.10), and each receiver's crowd
    // shares `[h][t][slots]`.
    uint64_t *hold;
    uint32_t *holdm;
    wide *sw, *sv;
    uint64_t *sc;
    uint64_t *ce;
    // The reverse's scratch: each head's and site's hold covector `[h][t]` and the crowds' difference
    // arrays over the places `[row][span]`.
    wide *lifts, *cv, *cw;
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

// A known site: resolved and carrying no mixture (its class arrived). The closure's holders are the
// known sites of a receiver's alphabet class (`holds`).
__device__ __forceinline__ bool known_site(const FieldWords &w, uint64_t g) {
    return w.unresolved[g] == 0 && w.mix_off[g] == w.mix_off[g + 1];
}

// A definite site (§14.1): known, or locked (a foil). Only definite sources are heard past the near
// field, and each class lists its definite members first.
__device__ __forceinline__ bool definite_site(const FieldWords &w, uint64_t g) {
    return w.definite[g] != 0;
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

// The skin decay itself, `D` on `2^(−30)`: the exact `1` of a still head.
__device__ __forceinline__ wide decay_raw(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d) {
    return still_head(w, h) ? (wide)1 : decay_of(w, h, l, d);
}

// A wide value carried across `d` sites by its skin decay: `release(D v, 30)` in a turned head, `v` in
// a still one (`decayed_wide`).
__device__ __forceinline__ wide carried_wide(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d, wide v) {
    return still_head(w, h) ? v : rel(decay_of(w, h, l, d) * v, MOVE_BITS);
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

// ---------------------------------------------------------------------------------------------
// the series row's carrier
//
// [definition; agent-inferred, November 1] **A row is summed whole in `L` limbs of 64 bits**
// (`FieldDeclaration::row_bits()` rounded up to limbs, §14.11): a signed sum is its two's complement
// modulo `2^(64 L)`, exact while the sum's magnitude is below `2^(64 L − 1)` (the declaration's bound,
// which no row passes). A term `face · mult · 2^(a − a_0)` is built once a pair and added whole; the
// current and a share are each one exact long division of such sums, to the nearest numerator.
template <int L>
struct Big {
    uint64_t v[L];
};

template <int L>
__device__ __forceinline__ Big<L> big_zero() {
    Big<L> r;
#pragma unroll
    for (int k = 0; k < L; k++) {
        r.v[k] = 0;
    }
    return r;
}

// `a += b` modulo `2^(64 L)`.
template <int L>
__device__ __forceinline__ void big_add(Big<L> &a, const Big<L> &b) {
    uint64_t carry = 0;
#pragma unroll
    for (int k = 0; k < L; k++) {
        const uint64_t s = a.v[k] + b.v[k];
        const uint64_t c1 = s < a.v[k] ? 1 : 0;
        const uint64_t t = s + carry;
        const uint64_t c2 = t < s ? 1 : 0;
        a.v[k] = t;
        carry = c1 | c2;
    }
}

template <int L>
__device__ __forceinline__ void big_add_small(Big<L> &a, uint64_t x) {
    uint64_t carry = x;
#pragma unroll
    for (int k = 0; k < L; k++) {
        const uint64_t t = a.v[k] + carry;
        carry = t < carry ? 1 : 0;
        a.v[k] = t;
    }
}

// `r = a − b`; returns the borrow out.
template <int L>
__device__ __forceinline__ uint64_t big_sub(Big<L> &r, const Big<L> &a, const Big<L> &b) {
    uint64_t borrow = 0;
#pragma unroll
    for (int k = 0; k < L; k++) {
        const uint64_t d = a.v[k] - b.v[k];
        const uint64_t b1 = a.v[k] < b.v[k] ? 1 : 0;
        const uint64_t e = d - borrow;
        const uint64_t b2 = d < borrow ? 1 : 0;
        r.v[k] = e;
        borrow = b1 | b2;
    }
    return borrow;
}

template <int L>
__device__ __forceinline__ void big_shr1(Big<L> &a) {
#pragma unroll
    for (int k = 0; k < L - 1; k++) {
        a.v[k] = (a.v[k] >> 1) | (a.v[k + 1] << 63);
    }
    a.v[L - 1] >>= 1;
}

template <int L>
__device__ __forceinline__ void big_negate(Big<L> &a) {
#pragma unroll
    for (int k = 0; k < L; k++) {
        a.v[k] = ~a.v[k];
    }
    big_add_small(a, 1);
}

// The binary length (`0` for zero).
template <int L>
__device__ __forceinline__ uint32_t big_bits(const Big<L> &a) {
    uint32_t bits = 0;
#pragma unroll
    for (int k = 0; k < L; k++) {
        if (a.v[k] != 0) {
            bits = 64 * k + bit_length(a.v[k]);
        }
    }
    return bits;
}

// `x << s` (bits shifted past the carrier are lost: the declaration's bound says there are none).
template <int L>
__device__ __forceinline__ Big<L> big_shl(const Big<L> &x, uint32_t s) {
    Big<L> r = big_zero<L>();
    const uint32_t q = s >> 6, b = s & 63;
#pragma unroll
    for (int qq = 0; qq < L; qq++) {
        if (q == (uint32_t)qq) {
#pragma unroll
            for (int k = qq; k < L; k++) {
                const int kk = k - qq;
                const int kp = kk > 0 ? kk - 1 : 0;
                const uint64_t carry = kk > 0 ? ((x.v[kp] >> 1) >> (63 - b)) : 0;
                r.v[k] = (x.v[kk] << b) | carry;
            }
        }
    }
    return r;
}

// A term's coefficient `face · mult`, three limbs (`face < 2^62`, `mult < 2^96`).
struct Coef {
    uint64_t c0, c1, c2;
};

__device__ __forceinline__ Coef coef_of(uint64_t face, uwide mult) {
    const uint64_t ml = (uint64_t)mult, mh = (uint64_t)(mult >> 64);
    const uwide p0 = (uwide)face * (uwide)ml;
    const uwide p1 = (uwide)face * (uwide)mh;
    const uwide mid = (p0 >> 64) + (uwide)(uint64_t)p1;
    Coef c;
    c.c0 = (uint64_t)p0;
    c.c1 = (uint64_t)mid;
    c.c2 = (uint64_t)(p1 >> 64) + (uint64_t)(mid >> 64);
    return c;
}

template <int L>
__device__ __forceinline__ Big<L> big_of(const Coef &c) {
    Big<L> r = big_zero<L>();
    r.v[0] = c.c0;
    r.v[1] = c.c1;
    r.v[2] = c.c2;
    return r;
}

// `c · m` with `m` of one limb, or two where `WIDE` (needs `L ≥ 5`).
template <int L, bool WIDE>
__device__ __forceinline__ Big<L> big_mul(const Coef &c, uint64_t m0, uint64_t m1) {
    Big<L> r = big_zero<L>();
    uwide t = (uwide)c.c0 * (uwide)m0;
    r.v[0] = (uint64_t)t;
    uint64_t carry = (uint64_t)(t >> 64);
    t = (uwide)c.c1 * (uwide)m0 + (uwide)carry;
    r.v[1] = (uint64_t)t;
    carry = (uint64_t)(t >> 64);
    t = (uwide)c.c2 * (uwide)m0 + (uwide)carry;
    r.v[2] = (uint64_t)t;
    r.v[3] = (uint64_t)(t >> 64);
    if (WIDE) {
        t = (uwide)c.c0 * (uwide)m1 + (uwide)r.v[1];
        r.v[1] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
        t = (uwide)c.c1 * (uwide)m1 + (uwide)r.v[2] + (uwide)carry;
        r.v[2] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
        t = (uwide)c.c2 * (uwide)m1 + (uwide)r.v[3] + (uwide)carry;
        r.v[3] = (uint64_t)t;
        r.v[4] = (uint64_t)(t >> 64);
    }
    return r;
}

// `⌊(num + ⌊M/2⌋) / M⌋`, the nearest quotient (half away from zero on a magnitude), by the shift-and-
// subtract long division over the quotient's bits; false where the quotient passes 64 bits.
template <int L>
__device__ bool big_div_nearest(Big<L> num, const Big<L> &M, uint64_t *quotient) {
    Big<L> half = M;
    big_shr1(half);
    big_add(num, half);
    const uint32_t nb = big_bits(num), mb = big_bits(M);
    if (nb < mb) {
        *quotient = 0;
        return true;
    }
    const uint32_t diff = nb - mb;
    if (diff > 63) {
        return false;
    }
    Big<L> mm = big_shl(M, diff);
    uint64_t q = 0;
    for (int b = (int)diff; b >= 0; b--) {
        Big<L> t;
        if (big_sub(t, num, mm) == 0) {
            num = t;
            q |= (uint64_t)1 << b;
        }
        big_shr1(mm);
    }
    *quotient = q;
    return true;
}

template <int L>
__device__ __forceinline__ Big<L> shfl_big(const Big<L> &x, int o) {
    Big<L> r;
#pragma unroll
    for (int k = 0; k < L; k++) {
        r.v[k] = (uint64_t)__shfl_xor_sync(0xffffffffu, (unsigned long long)x.v[k], o);
    }
    return r;
}

__device__ __forceinline__ int64_t warp_min_signed(int64_t v) {
    uint64_t key = (uint64_t)v ^ ((uint64_t)1 << 63);
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, key, o);
        key = w < key ? w : key;
    }
    return (int64_t)(key ^ ((uint64_t)1 << 63));
}

// A score's term (the host's `Field::face`, §14.11): its whole bits `a = ⌊z⌋` and the face of its
// fraction on `2^(−62)`, in `[2^61, 2^62)`.
__device__ __forceinline__ void term_of(const FieldWords &w, int64_t z, int64_t *a, uint64_t *face) {
    *a = z >> FACE_BITS;
    *face = below_one_face((wide)(z & (((int64_t)1 << FACE_BITS) - 1)) - ((wide)1 << FACE_BITS), w.face, w.digits);
}

// -------------------------------------------------------------------------------------------
// the resonance classes, the holds, the crowds and the prefix sums

// [definition; agent-inferred, November 1] **The resonance classes, their lists and the holds** (the
// dispersing field's §2.2, §6, §12 and §14.2; the host's `ClassLists::of` and `hold`): one block of one
// warp a head and a region. Each site's class is `Σ_l 3^l σ_l` over the shells of its unframed word's
// first `b` modes, listed under the key `2c` where it is definite (known or locked) and `2c + 1`
// otherwise; the counts are summed in the block's buckets, read as offsets in order, and the members
// placed by a stable counting sort, the region's sites in chunks of 32 in order, a lane its rank among
// the earlier lanes of its class (`__match_any_sync`), so class `c`'s members stand in ascending place
// exactly as the host lists them. Each site's hold is the least over those modes of `|re² − im²| /
// (re² + im²)` on `2^(−40)`, the first mode that sets it kept beside it.
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
            // The hold (`hold`): the first mode of least `λ_l`, `λ_l = div_nearest(|re² − im²| 2^40, re² + im²)`.
            uint64_t best = (uint64_t)1 << HOLD_BITS;
            uint32_t best_l = 0;
            for (uint32_t l = 0; l < w.ctrits; l++) {
                const wide re = word[l], im = word[w.M + l];
                const wide rr = re * re, ii = im * im;
                uint64_t lambda = 0;
                if (rr + ii != 0) {
                    wide diff = rr - ii;
                    diff = diff < 0 ? -diff : diff;
                    lambda = (uint64_t)div_nearest(diff << HOLD_BITS, rr + ii);
                }
                if (lambda < best) {
                    best = lambda;
                    best_l = l;
                }
            }
            w.cls[(uint64_t)h * w.T + g] = c;
            w.hold[(uint64_t)h * w.T + g] = best;
            w.holdm[(uint64_t)h * w.T + g] = best_l;
            atomicAdd(&buckets[2 * c + (definite_site(w, g) ? 0u : 1u)], 1u);
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
            const uint32_t c = live ? 2 * w.cls[(uint64_t)h * w.T + first + i] + (definite_site(w, first + i) ? 0u : 1u) : 0xFFFFFFFFu;
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

// [definition; agent-inferred, November 1] **The definite words' and values' prefix sums** (the host's
// `Sums::of`, §14.10), one head and region: `sw[row][x]`, `sv[row][x]` the sums of the definite sites'
// unit words and framed values before place `t` (`row = region_off[r] + r + t`, a region's `S + 1`
// rows), `sc[row]` their number. One thread an entry, each over its region's sites in order.
extern "C" __global__ void field_sums(FieldWords w) {
    const uint64_t per = 2 * (uint64_t)w.span + 1;
    const uint64_t threads = (uint64_t)w.H * w.R * per;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t u = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; u < threads; u += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t x = u % per;
        const uint64_t hr = u / per;
        const uint32_t r = hr % w.R, h = hr / w.R;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint64_t base = (uint64_t)h * rows1 + first + r;
        if (x < 2 * w.span) {
            const uint32_t xx = x % w.span;
            wide *out = (x < w.span ? w.sw : w.sv) + base * w.span + xx;
            const int64_t *src = (x < w.span ? w.qf : w.vf) + ((uint64_t)h * w.T + first) * w.span + xx;
            wide run = 0;
            out[0] = 0;
            for (uint32_t t = 0; t < sites; t++) {
                if (definite_site(w, first + t)) {
                    run += (wide)src[(uint64_t)t * w.span];
                }
                out[(uint64_t)(t + 1) * w.span] = run;
            }
        } else {
            uint64_t *out = w.sc + base;
            uint64_t run = 0;
            out[0] = 0;
            for (uint32_t t = 0; t < sites; t++) {
                run += definite_site(w, first + t) ? 1 : 0;
                out[t + 1] = run;
            }
        }
    }
}

// Site `i`'s support entry `k` of its region (the host's `ClassLists::support`, §14.1): the near field
// first (`k < NEAR_SLOTS`, the `NEAR − 1` places before and after it, nearest first), then the
// DEFINITE run of its class past the near field. Returns the source's place, or `UINT32_MAX` where the
// entry meets no site (a near place outside the region, or a member of the class inside the near field).
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

// A site's support length in entries (`NEAR_SLOTS` near places and the definite run of its class).
__device__ __forceinline__ uint32_t support_len(const uint32_t *off, uint32_t c) {
    return NEAR_SLOTS + off[2 * c + 1] - off[2 * c];
}

// Source `j`'s receiver entry `k`: the receivers that hear it. The near field, and where `j` is definite
// every member of its class past the near field (the support is directional: `j ∈ S_i` exactly when
// `j` is near `i`, or definite in `i`'s class).
__device__ __forceinline__ uint32_t receiver_at(const uint32_t *members, const uint32_t *off, uint32_t c, uint32_t j, uint32_t sites, uint32_t k) {
    return support_at(members, off, c, j, sites, k);
}

__device__ __forceinline__ uint32_t receiver_len(const uint32_t *off, uint32_t c, bool definite) {
    return NEAR_SLOTS + (definite ? off[2 * c + 2] - off[2 * c] : 0);
}

// Receiver `i`'s crowd `slot` in a region of `sites` (the host's `crowd_ranges`, §14.10): octave
// `level = 2 + ⌊slot/2⌋`, the nearer side first (even slots before `i`, odd after), the places
// `|i − j| ∈ [max(2^level, NEAR), 2^(level+1) − 1]` within the region. False where the crowd is absent.
__device__ __forceinline__ bool crowd_at(uint32_t i, uint32_t sites, uint32_t slot, uint32_t *lo, uint32_t *hi, uint32_t *level) {
    const uint32_t lv = 2 + slot / 2;
    if (lv >= 31 || ((uint32_t)1 << lv) >= sites) {
        return false;
    }
    const uint32_t near = max((uint32_t)1 << lv, (uint32_t)NEAR), far = ((uint32_t)2 << lv) - 1;
    if (slot % 2 == 0) {
        if (i < near) {
            return false;
        }
        *lo = i > far ? i - far : 0;
        *hi = i - near;
    } else {
        if (i + near >= sites) {
            return false;
        }
        *lo = i + near;
        *hi = min(i + far, sites - 1);
    }
    *level = lv;
    return true;
}

// The crowd slots a region of `sites` can hold (two an octave).
__device__ __forceinline__ uint32_t crowd_slots(uint32_t sites) {
    uint32_t slots = 0;
    for (uint32_t lv = 2; lv < 31 && ((uint32_t)1 << lv) < sites; lv++) {
        slots += 2;
    }
    return slots;
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

// A crowd's score (§14.10): its mean word at the octave's falloff, `div_nearest(Σ_l D_l (ŵ_il W_l +
// ŵ_i,n+l W_n+l), count 2^(16 + β + grain)) − level 2^16`, the words' sum `W` two reads of the prefix
// sums.
__device__ __forceinline__ int64_t crowd_score(const FieldWords &w, uint32_t h, const int64_t *wi, const wide *swlo, const wide *swhi, uint64_t count, uint32_t level) {
    wide score = 0;
    for (uint32_t l = 0; l < w.n; l++) {
        const wide d = decay_raw(w, h, l, (uint32_t)1 << level);
        score += d * ((wide)wi[l] * (swhi[l] - swlo[l]) + (wide)wi[w.n + l] * (swhi[w.n + l] - swlo[w.n + l]));
    }
    const uint32_t bits = (uint32_t)((int32_t)FACE_BITS + w.beta) + (still_head(w, h) ? 0 : MOVE_BITS);
    return fit64(div_nearest(score, (wide)count << bits) - ((wide)level << FACE_BITS), w.status);
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

// [definition; agent-inferred, November 1] **The contact, the series row and the current over each
// site's support** (`Field::tick`, §14.10, §14.11), one warp a head and a receiving site, the carrier
// `L` limbs. Pass one: the scores of the support and of the receiver's crowds and their least whole
// bits `a_0`. Pass two: each term `face · mult` shifted by `a − a_0` summed whole into the mass (the
// lanes over the terms) and, times each value entry, into the numerators (the lanes over the span's
// entries, a lane an entry and a part of the chunk), a far source's multiplier the product of both
// ends' holds, a crowd's mass multiplier its count. The numerators are divided once by the mass, to the
// nearest numerator, and returned to the receiver's frame. With `store`, the third pass forms each
// term's share of the mass, once, on `2^(−63)`: the pair's at the region block's dense address `[i][j]`
// (which held its score), a crowd's at `ce[h][t][slot]`. The pairs met are counted.
#define CONTACT_ROWS 8
template <int L>
__device__ void contact_body(const FieldWords &w, uint32_t store) {
    __shared__ uint64_t t0[CONTACT_ROWS][32], t1[CONTACT_ROWS][32], t2[CONTACT_ROWS][32];
    __shared__ uint32_t ts[CONTACT_ROWS][32], tj[CONTACT_ROWS][32];
    __shared__ uint32_t tlo[CONTACT_ROWS][32], thi[CONTACT_ROWS][32], tlv[CONTACT_ROWS][32];
    __shared__ int64_t crz[CONTACT_ROWS][32];
    __shared__ uint64_t crn[CONTACT_ROWS][32];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span;
    const uint32_t classes = w.nclasses;
    const bool narrow = w.bits[0] <= 31 && 2 * w.bits[0] + ceil_log2(S) <= 62;
    const uint32_t parts = span_parts(S);
    const uint32_t entry = lane % S, part = lane / S;
    const uint64_t rows = (uint64_t)w.H * w.T;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[(uint64_t)h * w.T + g];
        const uint32_t K = support_len(off, c);
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const int64_t *wi = words + (uint64_t)i * S;
        const uint64_t *holds = w.hold + (uint64_t)h * w.T + first;
        const uint64_t hi = holds[i];
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const wide *svp = w.sv + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = crowd_slots(sites);
        // Pass one: the least whole bits of the row's terms.
        int64_t amin = INT64_MAX;
        uint32_t met = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, c, i, sites, k);
            if (j != UINT32_MAX) {
                const int64_t z = contact_score(w, h, wi, words + (uint64_t)j * S, j > i ? j - i : i - j, narrow);
                const int64_t a = z >> FACE_BITS;
                amin = a < amin ? a : amin;
                met += 1;
            }
        }
        {
            uint64_t count = 0;
            int64_t z = 0;
            uint32_t lo, hi_, lv;
            if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                count = scp[hi_ + 1] - scp[lo];
                if (count != 0) {
                    z = crowd_score(w, h, wi, swp + (uint64_t)lo * S, swp + (uint64_t)(hi_ + 1) * S, count, lv);
                    const int64_t a = z >> FACE_BITS;
                    amin = a < amin ? a : amin;
                }
            }
            crz[warp][lane] = z;
            crn[warp][lane] = count;
        }
        amin = warp_min_signed(amin);
        if (amin == INT64_MAX) {
            amin = 0;
        }
        // Pass two: the terms summed whole.
        uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        Big<L> M = big_zero<L>();
        Big<L> N = big_zero<L>();
        uint32_t negs = 0;
        // The numerators of the chunk in the shared arrays (a pair's, or a crowd's when `crowd`).
        const auto numerators = [&](bool crowd) {
            if (part < parts) {
                for (uint32_t jj = part; jj < 32; jj += parts) {
                    const uint32_t j = tj[warp][jj];
                    if (j == UINT32_MAX) {
                        continue;
                    }
                    Coef cf;
                    cf.c0 = t0[warp][jj];
                    cf.c1 = t1[warp][jj];
                    cf.c2 = t2[warp][jj];
                    if ((cf.c0 | cf.c1 | cf.c2) == 0) {
                        continue;
                    }
                    Big<L> p;
                    bool neg;
                    if (!crowd) {
                        const uint32_t gap = j > i ? j - i : i - j;
                        const wide v = carried(w, h, entry % w.n, gap, values[(uint64_t)j * S + entry]);
                        neg = v < 0;
                        p = big_mul<L, false>(cf, mag64((int64_t)v), 0);
                    } else {
                        const uint32_t lo = tlo[warp][jj], hi_ = thi[warp][jj], lv = tlv[warp][jj];
                        const wide v = carried_wide(w, h, entry % w.n, (uint32_t)1 << lv, svp[(uint64_t)(hi_ + 1) * S + entry] - svp[(uint64_t)lo * S + entry]);
                        neg = v < 0;
                        const uwide m = (uwide)(neg ? -v : v);
                        p = big_mul<L, true>(cf, (uint64_t)m, (uint64_t)(m >> 64));
                    }
                    p = big_shl(p, ts[warp][jj]);
                    if (neg) {
#pragma unroll
                        for (int k = 0; k < L; k++) {
                            p.v[k] = ~p.v[k];
                        }
                        negs += 1;
                    }
                    big_add(N, p);
                }
            }
        };
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, c, i, sites, k) : UINT32_MAX;
            Coef cf = {0, 0, 0};
            uint32_t s = 0;
            if (j != UINT32_MAX) {
                const uint32_t gap = j > i ? j - i : i - j;
                const int64_t z = contact_score(w, h, wi, words + (uint64_t)j * S, gap, narrow);
                int64_t a;
                uint64_t face;
                term_of(w, z, &a, &face);
                const int64_t sh = a - amin;
                if (sh >= (int64_t)(64 * L)) {
                    atomicOr(w.status, REFUSED_CARRIER);
                } else {
                    s = (uint32_t)sh;
                }
                const uwide mult = gap < NEAR ? ((uwide)1 << (2 * HOLD_BITS)) : (uwide)hi * (uwide)holds[j];
                cf = coef_of(face, mult);
                big_add(M, big_shl(big_of<L>(cf), s));
                if (store) {
                    erow[j] = (uint64_t)z;
                }
            }
            t0[warp][lane] = cf.c0;
            t1[warp][lane] = cf.c1;
            t2[warp][lane] = cf.c2;
            ts[warp][lane] = s;
            tj[warp][lane] = j;
            __syncwarp();
            numerators(false);
            __syncwarp();
        }
        // The crowds' chunk: a crowd's value multiplier is `2^80`, its mass multiplier its count `2^80`.
        {
            const uint64_t count = crn[warp][lane];
            Coef cf = {0, 0, 0};
            uint32_t s = 0, slot = UINT32_MAX, lo = 0, hi_ = 0, lv = 0;
            if (count != 0 && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                slot = lane;
                int64_t a;
                uint64_t face;
                term_of(w, crz[warp][lane], &a, &face);
                const int64_t sh = a - amin;
                if (sh >= (int64_t)(64 * L)) {
                    atomicOr(w.status, REFUSED_CARRIER);
                } else {
                    s = (uint32_t)sh;
                }
                big_add(M, big_shl(big_of<L>(coef_of(face, (uwide)count << (2 * HOLD_BITS))), s));
                cf = coef_of(face, (uwide)1 << (2 * HOLD_BITS));
            }
            t0[warp][lane] = cf.c0;
            t1[warp][lane] = cf.c1;
            t2[warp][lane] = cf.c2;
            ts[warp][lane] = s;
            tj[warp][lane] = slot;
            tlo[warp][lane] = lo;
            thi[warp][lane] = hi_;
            tlv[warp][lane] = lv;
            __syncwarp();
            numerators(true);
            __syncwarp();
        }
        // The mass over the lanes; the numerators over the parts of each entry.
        for (int o = 16; o > 0; o >>= 1) {
            const Big<L> other = shfl_big(M, o);
            big_add(M, other);
        }
        for (uint32_t o = S; parts > 1 && o < 32; o <<= 1) {
            const Big<L> other = shfl_big(N, (int)o);
            big_add(N, other);
            negs += __shfl_xor_sync(0xFFFFFFFFu, negs, (int)o);
        }
        met = (uint32_t)warp_sum_u64(met);
        // The framed current's entry `entry`: the numerator over the mass, to the nearest numerator.
        int64_t y = 0;
        if (part == 0 && lane < S) {
            big_add_small(N, negs);
            const bool negative = (N.v[L - 1] >> 63) != 0;
            if (negative) {
                big_negate(N);
            }
            uint64_t q = 0;
            bool ok = big_div_nearest(N, M, &q);
            ok = ok && (negative ? q <= ((uint64_t)1 << 63) : q < ((uint64_t)1 << 63));
            if (ok) {
                y = (int64_t)(negative ? (uint64_t)0 - q : q);
            } else {
                atomicOr(w.status, REFUSED_WORD64);
            }
        }
        const int64_t yi = __shfl_sync(0xFFFFFFFFu, y, (lane + w.n) % 32);
        if (lane == 0) {
            atomicAdd(w.met, (unsigned long long)met);
        }
        if (lane < w.n) {
            wide ur, ui;
            frame_of(w, i, h, lane, &ur, &ui);
            const uint32_t m = h * w.n + lane;
            w.y[g * w.M2 + m] = fit64(rel(ur * (wide)y + ui * (wide)yi, MOVE_BITS), w.status);
            w.y[g * w.M2 + w.M + m] = fit64(rel(ur * (wide)yi - ui * (wide)y, MOVE_BITS), w.status);
        }
        // Pass three: each term's share of the mass, formed once.
        if (store) {
            for (uint32_t k = lane; k < K; k += 32) {
                const uint32_t j = support_at(members, off, c, i, sites, k);
                if (j != UINT32_MAX) {
                    const uint32_t gap = j > i ? j - i : i - j;
                    int64_t a;
                    uint64_t face;
                    term_of(w, (int64_t)erow[j], &a, &face);
                    const int64_t sh = a - amin;
                    const uwide mult = gap < NEAR ? ((uwide)1 << (2 * HOLD_BITS)) : (uwide)hi * (uwide)holds[j];
                    const Big<L> x = big_shl(big_of<L>(coef_of(face, mult)), (uint32_t)sh + SHARE_BITS);
                    uint64_t p = 0;
                    if (!big_div_nearest(x, M, &p)) {
                        p = UINT64_MAX;
                    }
                    erow[j] = p;
                }
            }
            uint64_t p = 0;
            uint32_t lo, hi_, lv;
            if (lane < w.slots && crn[warp][lane] != 0 && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                int64_t a;
                uint64_t face;
                term_of(w, crz[warp][lane], &a, &face);
                const int64_t sh = a - amin;
                const Big<L> x = big_shl(big_of<L>(coef_of(face, (uwide)crn[warp][lane] << (2 * HOLD_BITS))), (uint32_t)sh + SHARE_BITS);
                if (!big_div_nearest(x, M, &p)) {
                    p = UINT64_MAX;
                }
            }
            if (lane < w.slots) {
                w.ce[hg * w.slots + lane] = p;
            }
        }
    }
}

extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_l5(FieldWords w, uint32_t store) {
    contact_body<5>(w, store);
}
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_l6(FieldWords w, uint32_t store) {
    contact_body<6>(w, store);
}
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_l7(FieldWords w, uint32_t store) {
    contact_body<7>(w, store);
}
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_l8(FieldWords w, uint32_t store) {
    contact_body<8>(w, store);
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

// `δỹ = U ⊙ δy` by head: both `[h][t][2n]`.
extern "C" __global__ void field_current_back(FieldWords w, const int64_t *dy, int64_t *dyh) {
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
        dyh[at + li] = fit64(rel(ur * gr - ui * gi, MOVE_BITS), w.status);
        dyh[at + w.n + li] = fit64(rel(ui * gr + ur * gi, MOVE_BITS), w.status);
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

// [definition; agent-inferred, November 1] **The contact's return over one head's rows**, one warp a
// receiving site `i` (`Field::returned`, §14.2, §14.10, §14.11). Over its support, `δp_ij = ⟨δỹ_i, D ṽ_j⟩`,
// and for each crowd the same against its decayed mean value; the mean `μ_i = release(Σ p δp, 63)` over
// the pairs and the crowds; `δz = release(ln2 release(p (δp − μ), 63), 30)` and the closure's comparison
// (the holders are the known same-class pairs of an unresolved receiver at a closing tick), `δs =
// gained(δz, β)` held at the region block's dense address for the columns; a far pair's share without
// one end's hold, `p/λ`, returns the same comparison to that end's hold covector (`lifts`, summed with
// the ring's atomic step); and the word's row return `release(Σ δs D ŵ_j + Σ_C div_nearest(δs_C D W_C,
// |C|), 32)` written to its framed chart slot. A crowd's share of the values and of the word is spread
// over its members by the difference arrays `cv`, `cw` over the places.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_rows(FieldWords w, uint32_t h, uint32_t closes, const int64_t *dyh, wide *ds, int64_t *dq) {
    __shared__ wide dss[CONTACT_ROWS][32];
    __shared__ uint32_t js[CONTACT_ROWS][32];
    __shared__ wide dpcs[CONTACT_ROWS][32];
    __shared__ wide dsks[CONTACT_ROWS][32];
    __shared__ uint64_t cnts[CONTACT_ROWS][32];
    __shared__ Divisor cdivs[CONTACT_ROWS][32];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span;
    const uint32_t classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const uint32_t entry = lane % S, part = lane / S;
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    const bool still = still_head(w, h);
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t r = w.site_region[g];
        const uint32_t i = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[(uint64_t)h * w.T + g];
        const uint32_t K = support_len(off, c);
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        wide *dsr = ds + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *dyi = dyh + ((uint64_t)h * w.T + g) * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const uint64_t *holds_l = w.hold + (uint64_t)h * w.T + first;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const wide *svp = w.sv + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = crowd_slots(sites);
        // The closure (§19), over the support's pairs: on a still head at a closing tick, an unresolved
        // site's row is also compared with where its class stands among the sites it meets
        // (`closes` is the ring set's head count, zero where the head does not close). A carried site
        // holds nothing.
        const bool open = closes != 0 && w.unresolved[g] != 0;
        const uint32_t cls = w.classes[g];
        const auto holds = [&](uint32_t j) { return w.unresolved[first + j] == 0 && w.mix_off[first + j] == w.mix_off[first + j + 1] && w.classes[first + j] == cls; };
        // Pass A: δp over the pairs, held in the dense return; the weighted sum and the holders' share.
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
        // The crowds: δp against the decayed mean value, `div_nearest(Σ_x δỹ_x D V_x, |C|)`.
        {
            uint64_t count = 0;
            wide dpc = 0;
            uint32_t lo, hi_, lv;
            if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                count = scp[hi_ + 1] - scp[lo];
                if (count != 0) {
                    wide sum = 0;
                    for (uint32_t x = 0; x < S; x++) {
                        sum += (wide)dyi[x] * carried_wide(w, h, x % w.n, (uint32_t)1 << lv, svp[(uint64_t)(hi_ + 1) * S + x] - svp[(uint64_t)lo * S + x]);
                    }
                    cdivs[warp][lane] = divisor_of(count);
                    dpc = div_nearest_by(sum, cdivs[warp][lane]);
                    weighted += (wide)w.ce[(uint64_t)h * w.T * w.slots + g * w.slots + lane] * dpc;
                }
            }
            cnts[warp][lane] = count;
            dpcs[warp][lane] = dpc;
        }
        __syncwarp();
        const wide mean = rel(warp_sum(weighted), SHARE_BITS);
        const wide holders = warp_sum(held);
        const uint64_t copies = closes != 0 ? closes : 1;
        // `div_nearest(p 2^40, copies 2^63)` is two nested floors: `⌊(⌊(x + k/2)/2^63⌋)/copies⌋`.
        const bool hbig = holders > 0 && (uwide)holders * (uwide)copies > (uwide)UINT64_MAX;
        const Divisor hb = divisor_of(holders > 0 && !hbig ? (uint64_t)((uwide)holders * (uwide)copies) : 1);
        const wide hcopies = holders * (wide)copies;
        const wide cln2 = (wide)copies * ln2;
        const Divisor cl = divisor_of((uint64_t)cln2);
        const auto compare = [&](wide p, wide dpk, bool holder) -> wide {
            wide dz = rel(ln2 * rel(p * (dpk - mean), SHARE_BITS), MOVE_BITS);
            if (holders > 0) {
                const wide at = p << CONTACT_BITS;
                const wide a = (wide)(((uint64_t)((at + ((wide)copies << 62)) >> 63)) / copies);
                dz += a - (holder ? (hbig ? div_nearest(at, hcopies) : div_nearest_by(at, hb)) : 0);
            }
            return dz;
        };
        // A far pair's lift at one end: the pair's share without that end's hold, `r = div_nearest(p
        // 2^40, λ)`, times the same comparison (§14.2).
        const auto lift = [&](wide rr, wide dpk, bool holder) -> wide {
            wide gg = rel(rr * (dpk - mean), SHARE_BITS);
            if (holders > 0) {
                gg += div_nearest_by(rr << (CONTACT_BITS + MOVE_BITS - SHARE_BITS), cl) - (holder ? div_nearest(rr << (CONTACT_BITS + MOVE_BITS), hcopies * ln2) : 0);
            }
            return gg;
        };
        const uint64_t lam_i = holds_l[i];
        const Divisor li = divisor_of(lam_i > 0 ? lam_i : 1);
        wide lift_i = 0;
        // Pass B: δs over the pairs, in chunks of 32 into the warp's shared chunk, whose sum over the
        // word is read with the lanes over the span's entries.
        wide sum = 0;
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, c, i, sites, k) : UINT32_MAX;
            wide dz = 0;
            if (j != UINT32_MAX) {
                const uint32_t gap = j > i ? j - i : i - j;
                const wide p = (wide)e[j];
                const wide dpj = dsr[j];
                const bool holder = holds(j);
                dz = compare(p, dpj, holder);
                if (gap >= NEAR) {
                    const uint64_t lam_j = holds_l[j];
                    if (lam_i > 0) {
                        lift_i += lift(div_nearest_by(p << HOLD_BITS, li), dpj, holder);
                    }
                    if (lam_j > 0) {
                        add_wide(w.lifts + (uint64_t)h * w.T + first + j, lift(div_nearest(p << HOLD_BITS, (wide)lam_j), dpj, holder));
                    }
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
        lift_i = warp_sum(lift_i);
        if (lane == 0 && lift_i != 0) {
            add_wide(w.lifts + (uint64_t)h * w.T + g, lift_i);
        }
        // The crowds' δs, then their share of the word's row return and of the values' and the word's
        // member returns through the difference arrays.
        {
            wide dsk = 0;
            if (cnts[warp][lane] != 0) {
                dsk = gained(compare((wide)w.ce[(uint64_t)h * w.T * w.slots + g * w.slots + lane], dpcs[warp][lane], false), w.beta, w.status);
                if ((dsk < 0 ? -dsk : dsk) >> w.dsbits != 0) {
                    atomicOr(w.status, REFUSED_CARRIER);
                }
            }
            dsks[warp][lane] = dsk;
        }
        __syncwarp();
        if (part < parts) {
            for (uint32_t jj = part; jj < nslots; jj += parts) {
                if (cnts[warp][jj] == 0) {
                    continue;
                }
                uint32_t lo, hi_, lv;
                crowd_at(i, sites, jj, &lo, &hi_, &lv);
                const uint32_t l = entry % w.n;
                const wide d = decay_raw(w, h, l, (uint32_t)1 << lv);
                const Divisor &dv = cdivs[warp][jj];
                const wide dsk = dsks[warp][jj];
                sum += div_nearest_by(dsk * d * (swp[(uint64_t)(hi_ + 1) * S + entry] - swp[(uint64_t)lo * S + entry]), dv);
                const wide pw = div_nearest_by(dsk * d * (wide)words[(uint64_t)i * S + entry], dv);
                add_wide(w.cw + (first + r + lo) * S + entry, pw);
                add_wide(w.cw + (first + r + hi_ + 1) * S + entry, -pw);
                const wide pv = div_nearest_by((wide)w.ce[(uint64_t)h * w.T * w.slots + g * w.slots + jj] * carried(w, h, l, (uint32_t)1 << lv, dyi[entry]), dv);
                add_wide(w.cv + (first + r + lo) * S + entry, pv);
                add_wide(w.cv + (first + r + hi_ + 1) * S + entry, -pv);
            }
        }
        sum = parts_sum(part < parts ? sum : 0, S, parts);
        if (lane < S) {
            const uint32_t m = h * w.n + lane % w.n;
            dq[g * w.M2 + (lane < w.n ? m : w.M + m)] = fit64(rel(sum, CONTACT_BACK + (still ? 0 : MOVE_BITS)), w.status);
        }
    }
}

// [definition; agent-inferred, November 1] **The word's column return and the values' over one head**
// (`Field::returned`), one warp a source site `j` over its receivers (the support is directional: `j`
// is heard by its near field and, where `j` is definite, by every member of its class):
// `δw̃_j += release(Σ_i δs_ij D w̃_i, 32)` added to the rows' return in its framed chart slot, and
// `δṽ_j = release(Σ_i p_ij D δỹ_i, 63)`, the lanes over the span's entries (a lane an entry and a part
// of the receivers), `p_ij` and `δs_ij` read at the region block's dense address `[i][j]`.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_columns(FieldWords w, uint32_t h, const int64_t *dyh, const wide *ds, int64_t *dq, int64_t *dv) {
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
        const uint32_t K = receiver_len(off, c, definite_site(w, g));
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + j;
        const wide *dsc = ds + w.region_eoff[r] + j;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *dyr = dyh + ((uint64_t)h * w.T + first) * S;
        wide sk = 0, sv = 0;
        const bool still = still_head(w, h);
        if (part < parts) {
            for (uint32_t k = part; k < K; k += parts) {
                const uint32_t i = receiver_at(members, off, c, j, sites, k);
                if (i == UINT32_MAX) {
                    continue;
                }
                const uint64_t at = (uint64_t)i * sites;
                const uint32_t gap = j > i ? j - i : i - j;
                const wide term = dsc[at] * (wide)words[(uint64_t)i * S + entry];
                sk += still ? term : term * decay_of(w, h, entry % w.n, gap);
                sv += (wide)e[at] * carried(w, h, entry % w.n, gap, dyr[(uint64_t)i * S + entry]);
            }
        }
        sk = parts_sum(part < parts ? sk : 0, S, parts);
        sv = parts_sum(part < parts ? sv : 0, S, parts);
        if (lane < S) {
            const uint32_t m = h * w.n + lane % w.n;
            const uint64_t slot = g * w.M2 + (lane < w.n ? m : w.M + m);
            dq[slot] = fit64((wide)dq[slot] + rel(sk, CONTACT_BACK + (still ? 0 : MOVE_BITS)), w.status);
            dv[slot] = fit64(rel(sv, SHARE_BITS), w.status);
        }
    }
}

// The crowds' members' share (§14.10): the difference arrays `cv`, `cw` summed over the places (the
// host's `spread`), added at the definite sites only, each released as its own sum:
// `dv = fit64(dv + release(Σ cv, 63))`, `dq = fit64(dq + release(Σ cw, 32))`. One thread an entry of the
// span and a region, each over its region's sites in order.
extern "C" __global__ void field_spread(FieldWords w, uint32_t h, int64_t *dq, int64_t *dv) {
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    (void)rows1;
    const bool still = still_head(w, h);
    for (uint64_t u = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; u < (uint64_t)w.R * w.span; u += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = u / w.span, x = u % w.span;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        wide runv = 0, runw = 0;
        for (uint32_t t = 0; t < sites; t++) {
            const uint64_t row = first + r + t;
            runv += w.cv[row * w.span + x];
            runw += w.cw[row * w.span + x];
            if (definite_site(w, first + t)) {
                const uint32_t m = h * w.n + x % w.n;
                const uint64_t slot = (first + t) * w.M2 + (x < w.n ? m : w.M + m);
                dq[slot] = fit64((wide)dq[slot] + rel(runw, CONTACT_BACK + (still ? 0 : MOVE_BITS)), w.status);
                dv[slot] = fit64((wide)dv[slot] + rel(runv, SHARE_BITS), w.status);
            }
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

// [definition; agent-inferred, November 1] **A hold's return to its mode** (the host's `hold_return`,
// §14.2): with `N = re² − im²`, `D = re² + im²`, `s = sign N`, a hold covector `G` on `2^(−40)` returns
// `div_nearest(±4 s G re im², D²)` on the covector's `2^(−24)`, added at the unframed word's mode that
// sets the hold (its slots `h n + l` and `M + h n + l`). A product past its carrier is refused. One
// thread a head and a site.
extern "C" __global__ void field_hold_back(FieldWords w, int64_t *dq) {
    const uint64_t cells = (uint64_t)w.H * w.T;
    for (uint64_t u = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; u < cells; u += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t h = u / w.T;
        const uint64_t t = u % w.T;
        const uint64_t lambda = w.hold[u];
        const wide gg = w.lifts[u];
        if (gg == 0 || lambda == 0) {
            continue;
        }
        const uint32_t l = w.holdm[u];
        const uint32_t c = h * w.n + l;
        const wide re = w.qkv[t * 2 * w.M2 + c], im = w.qkv[t * 2 * w.M2 + w.M + c];
        const wide rr = re * re, ii = im * im;
        const wide d = rr + ii;
        const wide sign = (rr - ii) > 0 ? 1 : ((rr - ii) < 0 ? -1 : 0);
        const auto bits = [](wide v) -> uint32_t {
            const uwide m = (uwide)(v < 0 ? -v : v);
            const uint64_t hi = (uint64_t)(m >> 64);
            return hi != 0 ? 128 - __clzll((long long)hi) : (m == 0 ? 0 : 64 - __clzll((long long)(uint64_t)m));
        };
        if (sign == 0) {
            continue;
        }
        if (2 * bits(d) > 126 || bits(gg) + max(bits(re) + bits(ii), bits(im) + bits(rr)) + 3 > 126) {
            atomicOr(w.status, REFUSED_CARRIER);
            continue;
        }
        const wide dre = div_nearest(4 * sign * gg * re * ii, d * d);
        const wide dim = div_nearest(-4 * sign * gg * im * rr, d * d);
        const uint64_t at = t * w.M2 + c;
        dq[at] = fit64((wide)dq[at] + dre, w.status);
        dq[at + w.M] = fit64((wide)dq[at + w.M] + dim, w.status);
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
