#pragma once

#include <holonics/codec/algebraic_variation_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_algebraic_variation_explanation(
    const algebraic_variation_surface& surface, variation_explanation& out) noexcept {
  if (surface.passage.value() == 0 || !surface.family_exact || !surface.connection_exact ||
      !surface.invariant_exact || !surface.operator_exact || !surface.loops_exact ||
      !surface.selection_exact || !surface.alternatives_retained) { return false; }
  out.identity = exact::word{127'601}; out.passage = surface.passage;
  return append_blind(out.bytes, out.byte_count,
      "The coefficient family first separates into three affine root currents. Their pairwise "
      "collisions return a doubled singular divisor; that multiplicity is not collapsed into its "
      "reduced pole support. Exact reductions of two differential forms then return a rank-two "
      "rational transport law. Intersecting its characteristic constraints across discovery and "
      "held-out fibers leaves an oriented alternating form, while local, Euclidean, symmetric, "
      "and degenerate alternatives retain their failed residuals. Eliminating one transported "
      "component returns a scalar differential current and, independently, its exact coefficient "
      "recurrence. The two collision occurrences act as distinct noncommuting transvections even "
      "though their spectra agree; the ordered third return closes their loop product. The proof "
      "passage is selected only after these family, reduction, connection, pairing, operator, and "
      "loop dependencies close together. Under the separately declared smooth degree-two-cover and "
      "Picard--Lefschetz hypotheses this is a bounded variation-of-Hodge witness. It is not a proof "
      "of the general Picard--Fuchs theorem, the Hodge conjecture, or any RH consequence.");
}

}  // namespace holonics::codec
