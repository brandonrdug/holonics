#pragma once

#include <holonics/codec/causal_linear_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_causal_linear_explanation(
    const causal_linear_surface& surface, causal_linear_explanation& out) noexcept {
  if (surface.passage.value() == 0 || !surface.chain_exact ||
      !surface.characteristics_exact || !surface.multilinear_exact ||
      !surface.controls_exact || !surface.alternatives_retained) { return false; }
  out.identity = exact::word{128'601}; out.passage = surface.passage;
  return append_blind(out.bytes, out.byte_count,
      "Four source geometries cross one exact calculus rather than four presentation-specific "
      "summaries. The cyclic product returns its complete cellular boundary and homology; the "
      "cyclotomic incidence crystal returns graph boundary, cycle space, and the same adjacency "
      "characteristic through an independent common carrier; the fan character maps return their "
      "determinantal divisors and the star subdivision returns a new free direction with an "
      "exceptional negative face; and the varying cubic returns its rank-jump pencil, alternating "
      "adjoints, exterior determinant, and tensor transport. Equal characteristic polynomials "
      "remain compatible with unequal fixed fibers, equal ranks retain differently placed "
      "kernels, and conjugate presentations retain their lineage. The rotation control refuses a "
      "rational eigenvalue but returns an exact eigenpair after the Gaussian coefficient extension. "
      "Thus characteristic placement is useful only beside its module, coefficient field, source "
      "incidence, and transported form. This bounded result is an instrument for later intrinsic "
      "hypergeometry; it is not a universal tensor calculus, Hodge realization, or RH evidence.");
}

}  // namespace holonics::codec
