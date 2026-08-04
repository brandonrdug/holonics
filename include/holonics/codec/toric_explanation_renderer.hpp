#pragma once

#include <holonics/codec/toric_cycle_face.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_toric_explanation(
    const toric_cycle_surface& surface, toric_explanation& out) noexcept {
  if (surface.passage.value() == 0 || !surface.fan_chow_agree ||
      !surface.inverse_fibers_exact || !surface.blowup_transport_exact ||
      !surface.alternatives_retained) { return false; }
  out.identity = exact::word{127'501};
  out.passage = surface.passage;
  return append_blind(out.bytes, out.byte_count,
      "The ordered primitive rays determine complete smooth fans, their character relations, "
      "and torsion-free divisor-class quotients without receiving a variety name or a basis. "
      "Independent fan-local and Chow-reduction passages return the same intersection form. "
      "Exact congruence, rather than matrix eigenvalue presentation, returns its inertia and "
      "separates the positive anticanonical direction from primitive negative controls. Under "
      "the declared standard toric comparison hypotheses, the bounded Betti and Hodge receiver "
      "ranks are attached separately from the constructed arithmetic. Response inversion returns "
      "an integral fiber, a rational fiber with no integral "
      "member, and an incompatible obstruction. The selected cone itself derives the star ray; "
      "every strict and total transform is retained, the resulting exceptional class has square "
      "minus one, and pullback, pushforward, their kernels and images, and the projection formula "
      "agree. These are bounded toric-surface constructions and do not assert "
      "the Hodge conjecture or any Riemann-hypothesis consequence.");
}

}  // namespace holonics::codec
