#pragma once

#include <holonics/codec/expression_geometry_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_expression_geometry_explanation(
    const expression_geometry_surface& source,
    expression_geometry_explanation& out) noexcept {
  if (source.passage.value() == 0 || !source.ideals_exact || !source.differential_exact ||
      !source.residue_exact || !source.fibers_exact || !source.changed_sensitive ||
      !source.alternatives_retained) { return false; }
  out.identity = exact::word{128'801}; out.passage = source.passage;
  return append_blind(out.bytes, out.byte_count,
      "The mounted symbols did not arrive with a variety, singular locus, differential basis, "
      "or named equation. Their own sparse incidence produced the Jacobian stratum, five node "
      "occurrences over its algebraic fiber, a rank-four differential carrier, its exact "
      "connection, and the fourth-order characteristic passage. The finite repeated exponent and "
      "nonzero square-zero residue expose the logarithmic continuation channel without choosing a "
      "decimal collision root. The expanded chart returns to the same rational geometry after a "
      "discovered translation. The sign twist reaches the same discriminant and scalar receiver "
      "but not the same rational source fiber; only the declared Gaussian field port closes that "
      "passage. Changing the source constant rebuilds the Jacobian, discriminant, connection, and "
      "series. The expression has therefore become a navigable causal geometry rather than a "
      "string awaiting a supplied hypergeometric name. This bounded return is not Hodge or RH.");
}

}  // namespace holonics::codec
