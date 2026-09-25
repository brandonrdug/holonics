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
