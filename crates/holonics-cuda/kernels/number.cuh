// **The number of the theory on the card** (step 2 of the number record's build order; the host owner is
// `holonics::number`, the typed realization `holonics::number::word`).
//
// [definition] A word is `L` limbs of 32 places, little-endian: its unsigned reading is a residue on a path of `32L`
// places, its signed reading the same residue in the two's-complement section. Every operation returns what the host
// owner returns: a sum or difference on the path with its winding (the carry or borrow that left the top place), the
// signed winding of the two's-complement reading (−1, 0 or 1), a product at twice the places by columns (Comba: each
// column's products summed in a 96-place bond, as wide as the bits of its count of terms need, then one carry), the
// release of `k` places to the nearest, ties up, with its remainder (`x = q·2^k + r`, `−2^(k−1) ≤ r < 2^(k−1)`), and the
// bottom end of the inversion, Hensel from `x₀ = (3a) ⊕ 2` with its residual carried (`X′ = X(1 + E)`, `E′ = E²`) until `E`
// vanishes modulo `2^(32L)`.
//
// [definition] **Wide values cooperate across a warp** (the number record's §9.4): each lane holds one limb, a ballot
// reads each lane's generate `g` (its limbs' sum carried) and propagate `p` (its sum all ones), and the carries into the
// limbs are `((g | p) + g) ⊕ p` (with `X = g | p`, `Y = g`: `X ∧ Y = g`, `X ⊕ Y = p`, so the carries of `X + Y` are the
// adder's), one 32-place addition for 1,024 places.
//
// [definition] **Narrow values pack several to a word with their carry edges cut** (receipt L3): with `H` each field's top
// place, `((x ∧ ¬H) + (y ∧ ¬H)) ⊕ ((x ⊕ y) ∧ H)` adds every field on its own path.

#pragma once
#include <stdint.h>

template <int L>
struct hn_word {
    uint32_t w[L];
};

// The sum on the path of 32L places; returns the carry out of the top limb (the winding of the unsigned reading).
template <int L>
__device__ __forceinline__ uint32_t hn_add(hn_word<L>& r, const hn_word<L>& a, const hn_word<L>& b) {
    uint64_t c = 0;
#pragma unroll
    for (int i = 0; i < L; ++i) {
        const uint64_t s = (uint64_t)a.w[i] + b.w[i] + c;
        r.w[i] = (uint32_t)s;
        c = s >> 32;
    }
    return (uint32_t)c;
}

// The difference on the path; returns the borrow out of the top limb (the unsigned reading's winding is its negation).
template <int L>
__device__ __forceinline__ uint32_t hn_sub(hn_word<L>& r, const hn_word<L>& a, const hn_word<L>& b) {
    uint32_t borrow = 0;
#pragma unroll
    for (int i = 0; i < L; ++i) {
        const uint64_t s = (uint64_t)a.w[i] - b.w[i] - borrow;
        r.w[i] = (uint32_t)s;
        borrow = (uint32_t)(s >> 63);
    }
    return borrow;
}

// The signed winding of a sum already formed: −1, 0 or 1, the turns the two's-complement class made past its section.
template <int L>
__device__ __forceinline__ int hn_signed_winding(const hn_word<L>& a, const hn_word<L>& b, const hn_word<L>& r) {
    const uint32_t sa = a.w[L - 1] >> 31, sb = b.w[L - 1] >> 31, sr = r.w[L - 1] >> 31;
    if (sa == sb && sr != sa) {
        return sa ? -1 : 1;
    }
    return 0;
}

// The unsigned product at 64L places, by columns.
template <int L>
__device__ __forceinline__ void hn_mul(hn_word<2 * L>& r, const hn_word<L>& a, const hn_word<L>& b) {
    uint64_t lo = 0;
    uint32_t hi = 0;
#pragma unroll
    for (int k = 0; k < 2 * L - 1; ++k) {
#pragma unroll
        for (int i = 0; i < L; ++i) {
            const int j = k - i;
            if (j >= 0 && j < L) {
                const uint64_t p = (uint64_t)a.w[i] * b.w[j];
                lo += p;
                hi += lo < p;
            }
        }
        r.w[k] = (uint32_t)lo;
        lo = (lo >> 32) | ((uint64_t)hi << 32);
        hi = 0;
    }
    r.w[2 * L - 1] = (uint32_t)lo;
}

// The low half of the product: the product on the path of 32L places.
template <int L>
__device__ __forceinline__ void hn_mul_low(hn_word<L>& r, const hn_word<L>& a, const hn_word<L>& b) {
    uint64_t lo = 0;
    uint32_t hi = 0;
#pragma unroll
    for (int k = 0; k < L; ++k) {
#pragma unroll
        for (int i = 0; i <= k; ++i) {
            const uint64_t p = (uint64_t)a.w[i] * b.w[k - i];
            lo += p;
            hi += lo < p;
        }
        r.w[k] = (uint32_t)lo;
        lo = (lo >> 32) | ((uint64_t)hi << 32);
        hi = 0;
    }
}

// The signed product at 64L places: the unsigned product less each negative operand's partner shifted 32L places.
template <int L>
__device__ __forceinline__ void hn_mul_signed(hn_word<2 * L>& r, const hn_word<L>& a, const hn_word<L>& b) {
    hn_mul<L>(r, a, b);
    hn_word<L> top;
#pragma unroll
    for (int i = 0; i < L; ++i) top.w[i] = r.w[L + i];
    if (a.w[L - 1] >> 31) hn_sub<L>(top, top, b);
    if (b.w[L - 1] >> 31) hn_sub<L>(top, top, a);
#pragma unroll
    for (int i = 0; i < L; ++i) r.w[L + i] = top.w[i];
}

// Place `p`'s bit of a word read with one extra sign place above its top (`sign` the 33rd... place's bit).
template <int L>
__device__ __forceinline__ uint32_t hn_bit(const hn_word<L>& x, uint32_t sign, int p) {
    return p >= 32 * L ? sign : (x.w[p >> 5] >> (p & 31)) & 1u;
}

// **The release** of `k` places (0 < k < 32L) of a signed word to the nearest, ties up: `x = q·2^k + r`. The sum
// `t = x + 2^(k−1)` is read at 32L + 1 places (its extra place the true sign), `q = t >> k` (arithmetic) and
// `r = (t mod 2^k) − 2^(k−1)`.
template <int L>
__device__ __forceinline__ void hn_release_nearest(hn_word<L>& q, hn_word<L>& r, const hn_word<L>& x, int k) {
    hn_word<L> half;
#pragma unroll
    for (int i = 0; i < L; ++i) half.w[i] = 0;
    half.w[(k - 1) >> 5] = 1u << ((k - 1) & 31);
    hn_word<L> t;
    hn_add<L>(t, x, half);
    // The true sign of x + 2^(k−1): x's own where the sum stayed in the section, else the opposite of the word's top.
    const uint32_t sx = x.w[L - 1] >> 31, st = t.w[L - 1] >> 31;
    const uint32_t sign = (sx == 0 && st == 1) ? 0u : st;
    // q = t >> k, arithmetic, from the 32L + 1 place reading.
#pragma unroll
    for (int i = 0; i < L; ++i) {
        uint32_t limb = 0;
        for (int b = 0; b < 32; ++b) limb |= hn_bit<L>(t, sign, 32 * i + b + k) << b;
        q.w[i] = limb;
    }
    // r = (t mod 2^k) − 2^(k−1): the low k places, less half, sign-extended.
    hn_word<L> low;
#pragma unroll
    for (int i = 0; i < L; ++i) {
        const int base = 32 * i;
        low.w[i] = base >= k ? 0u : (k - base >= 32 ? t.w[i] : t.w[i] & ((1u << (k - base)) - 1u));
    }
    hn_sub<L>(r, low, half);
}

// **The bottom end of the inversion** for an odd word: X with a·X ≡ 1 (mod 2^(32L)), the residual carried; returns the
// steps taken (four at 64 places).
template <int L>
__device__ __forceinline__ int hn_invert_bottom(hn_word<L>& x, const hn_word<L>& a) {
    hn_word<L> three, one, e, t;
#pragma unroll
    for (int i = 0; i < L; ++i) {
        three.w[i] = 0;
        one.w[i] = 0;
    }
    three.w[0] = 3;
    one.w[0] = 1;
    hn_mul_low<L>(x, a, three);
    x.w[0] ^= 2u;
    hn_mul_low<L>(t, a, x);
    hn_sub<L>(e, one, t);
    int certified = 5, steps = 0;
    while (certified < 32 * L) {
        hn_word<L> onee;
        hn_add<L>(onee, one, e);
        hn_mul_low<L>(t, x, onee);
        x = t;
        hn_mul_low<L>(t, e, e);
        e = t;
        certified *= 2;
        ++steps;
    }
    return steps;
}

// The cut add on packed fields of one 32-place word, `H` each field's top place.
__device__ __forceinline__ uint32_t hn_cut_add(uint32_t x, uint32_t y, uint32_t h) {
    return ((x & ~h) + (y & ~h)) ^ ((x ^ y) & h);
}

// **The warp's add** of two 1,024-place words, lane `i` holding limb `i` of each: returns this lane's limb of the sum,
// and the carry out of the top limb in `winding` (every lane reads it).
__device__ __forceinline__ uint32_t hn_warp_add(uint32_t a, uint32_t b, uint32_t& winding) {
    const uint32_t lane = threadIdx.x & 31u;
    const uint32_t s = a + b;
    const uint32_t g = __ballot_sync(0xffffffffu, s < a);
    const uint32_t p = __ballot_sync(0xffffffffu, s == 0xffffffffu);
    const uint64_t sum = (uint64_t)(g | p) + g;
    const uint32_t carries = (uint32_t)sum ^ p;
    winding = (uint32_t)(sum >> 32);
    return s + ((carries >> lane) & 1u);
}
