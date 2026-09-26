// **The signed 128-bit word ring and its carrier refusal** (#12, #76).
//
// Ported from `13f8c734:crates/holonics-cuda/kernels/exact_resident_section.cu` (its `wide`
// carrier: the exact magnitude of the signed minimum, the product of two words, the refusal bit)
// and `13f8c734:crates/holonics-cuda/kernels/exact_integer.cuh` (the signed-magnitude carrier
// with an explicit overflow flag), rewritten against today's objects and cut to what the HNN
// consumes. History's directed shifts, dyadic scaling, integer square roots, 256-bit products,
// multi-limb `ExactInteger<N>` and the per-operation checked adds are not consumed by any HNN
// kernel today and are not ported.
//
// [definition] **The ring.** A word is an element of Z/2^128 in two's complement: `uwide`
// addition and `wide` products of two signed 64-bit words are the ring's operations, and they
// wrap by definition (unsigned arithmetic; the signed reading of an unsigned word is modular in
// C++20). The **carrier** is the symmetric window W = (−2^127, 2^127), closed under negation; a
// word is read as an integer only on W.
//
// [definition] **The certificate is the l1 bound.** For integers p_1 … p_n with
// Σ_j |p_j| < 2^127, every partial sum, in every order and every tree of the reduction, has
// magnitude at most Σ_j |p_j|, so it lies in W, and the ring's sum read on W is the integer sum.
// A reduction therefore carries, beside its ring word, the sum of its terms' magnitudes,
// saturated at 2^127; the word is read only when that bound is below 2^127, and is refused
// otherwise, **whatever its value**. The refusal is a property of the exact terms alone, never of
// the realization's order: the device and any host reference refuse the same reads. It is the
// lattice rule's own quantity (`holonics::hnn::FieldDeclaration::lattice_by_rule`: `X_l`, the
// declared bound on the l1 norm of the operand one read of a locus sums), read at the carrier.
//
// A product of two signed 64-bit words has magnitude at most 2^126 (the signed minimum squared),
// so it is always a word of W and needs no refusal; the magnitude of the signed minimum is taken
// as `(uwide)0 − (uwide)v`, which is exact where a signed negation would overflow.
//
// [definition] **The certificate extended to products of two bounded operands.** A signed 64-bit
// word `a` times a certified carrier word `b` (`|b| < 2^127`, itself the read of a certified sum)
// can reach 2^190. Its magnitude is formed exactly from the limbs of `|b|`, and the product is a
// term of the ring only when `|a|·|b| < 2^127`; otherwise its magnitude enters the certificate
// saturated, so the sum it joins is refused whatever its value (`hnn_bounded_product`). The rule
// is again a property of the exact terms alone.
//
// [definition] **The nearest-point split** (`hnn_nearest`): Lean `HNN/LatticeDeposit.quot`/`rem`,
// the nearest multiple of `2^L`, ties upward, `s = q·2^L + r` with `−2^(L−1) ≤ r < 2^(L−1)`; at
// `L = 0` every integer is a lattice point and `r = 0`. It is read off the low bits and the
// arithmetic shift (the floor, C++20), with no addition that could leave the carrier.
//
// [definition] **The word boundary of a result.** A state or chart coordinate the split produces
// is kept only when it is a signed 64-bit word, the width every operand enters the card at;
// otherwise the entry is refused (`HNN_REFUSED_WORD`), never wrapped. An entry that reads a
// refused operand is refused in turn (`HNN_REFUSED_OPERAND`), so a refusal travels with the
// current and is reported where the word is released.
//
// [open] The ring law's formal statement (the Z/2^w residue read on (−2^(w−1), 2^(w−1)) equals
// the integer sum under the l1 certificate) is owed in #62; it is elementary and has no Lean
// counterpart in `lean/` yet.

#pragma once
#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

// A read's status word: zero is exact; each refusal is one bit.
#define HNN_EXACT 0u
#define HNN_REFUSED_CARRIER 1u
#define HNN_REFUSED_MALFORMED 2u
#define HNN_REFUSED_WORD 4u
#define HNN_REFUSED_OPERAND 8u

// 2^127: the least magnitude outside the carrier.
#define HNN_CARRIER_BOUND (((uwide)1) << 127)

// |v| as an unsigned magnitude, exact for the signed minimum.
__device__ __forceinline__ uwide hnn_magnitude(wide v) {
    return v < 0 ? (uwide)0 - (uwide)v : (uwide)v;
}

// The product of two signed 64-bit words: exact, |p| ≤ 2^126.
__device__ __forceinline__ wide hnn_word_product(int64_t a, int64_t b) {
    return (wide)a * (wide)b;
}

// The certificate's addition: the l1 bounds of two parts, saturated at 2^127. Both operands are
// at most 2^127, so the sum of two unsaturated bounds stays below 2^128 and cannot wrap.
__device__ __forceinline__ uwide hnn_certify(uwide bound, uwide magnitude) {
    if (bound >= HNN_CARRIER_BOUND || magnitude >= HNN_CARRIER_BOUND) {
        return HNN_CARRIER_BOUND;
    }
    const uwide sum = bound + magnitude;
    return sum >= HNN_CARRIER_BOUND ? HNN_CARRIER_BOUND : sum;
}

// Read a ring word as an integer under its certificate, or refuse the carrier.
__device__ __forceinline__ wide hnn_certified(uwide word, uwide bound, uint32_t *status) {
    if (bound >= HNN_CARRIER_BOUND) {
        *status |= HNN_REFUSED_CARRIER;
        return 0;
    }
    return (wide)word;
}

// The product of a signed 64-bit word and a carrier word (|b| < 2^127): the exact product and its
// magnitude when |a·b| < 2^127; otherwise the magnitude saturates at 2^127 and the product is
// unread (zero). With |b| = h·2^64 + l: |a|·l < 2^127 and |a|·h < 2^126; |a|·h ≥ 2^63 already
// puts the product past 2^127, and below it (|a|·h)·2^64 + |a|·l < 2^128 cannot wrap.
__device__ __forceinline__ wide hnn_bounded_product(int64_t a, wide b, uwide *magnitude) {
    const uwide ma = hnn_magnitude((wide)a);
    const uwide mb = hnn_magnitude(b);
    const uwide limb = ((uwide)1 << 64) - 1;
    const uwide high = ma * (mb >> 64);
    if (high >= ((uwide)1 << 63)) {
        *magnitude = HNN_CARRIER_BOUND;
        return 0;
    }
    const uwide m = (high << 64) + ma * (mb & limb);
    if (m >= HNN_CARRIER_BOUND) {
        *magnitude = HNN_CARRIER_BOUND;
        return 0;
    }
    *magnitude = m;
    return ((a < 0) != (b < 0)) ? -(wide)m : (wide)m;
}

// The nearest-point split of a carrier word at 2^shift, ties upward (shift ≤ 127): returns q and
// writes r, s = q·2^shift + r, −2^(shift−1) ≤ r < 2^(shift−1).
__device__ __forceinline__ wide hnn_nearest(wide s, uint32_t shift, wide *remainder) {
    if (shift == 0) {
        *remainder = 0;
        return s;
    }
    const uwide unit = (uwide)1 << shift;
    const uwide low = (uwide)s & (unit - 1);
    const wide below = s >> shift;  // the floor of s / 2^shift
    if (low >= (unit >> 1)) {
        *remainder = (wide)(low - unit);  // in [−2^(shift−1), 0), read modularly
        return below + 1;
    }
    *remainder = (wide)low;
    return below;
}

// Whether an integer is a signed 64-bit word.
__device__ __forceinline__ bool hnn_is_word(wide v) {
    return v >= (wide)INT64_MIN && v <= (wide)INT64_MAX;
}

// The block's tree over its threads' ring words and certificates (blockDim.x a power of two):
// ring addition and the saturated certificate addition are associative and commutative, so the
// tree's order changes no value and no refusal. Thread 0 holds the block's word and bound.
__device__ __forceinline__ void hnn_block_sum(uwide *ring, uwide *bound, uint32_t t) {
    for (uint32_t stride = blockDim.x >> 1; stride > 0; stride >>= 1) {
        if (t < stride) {
            ring[t] += ring[t + stride];
            bound[t] = hnn_certify(bound[t], bound[t + stride]);
        }
        __syncthreads();
    }
}
