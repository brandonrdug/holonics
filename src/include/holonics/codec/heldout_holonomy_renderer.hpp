#pragma once

#include <holonics/codec/elementary_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_heldout_holonomy(
    const heldout_holonomy_surface &surface, elementary_formal_face &face) noexcept {
  using rederivation_render_detail::writer; using namespace elementary_render_detail;
  writer out{face}; face.identity = exact::word{199'411}; face.passage = surface.passage;
  if (!surface.exact || !surface.prediction_before_comparison || !surface.source_detached ||
      !out.text("import R32_ELEMENTARY_CAUSAL_CALCULUS\n\nnamespace Soma.Holonics.R32\n\n"
      "def heldoutTriangleProduct : ExactMatrix2 := ") || !matrix(out,surface.product) ||
      !out.text("\n\ndef heldoutTriangleTrace : List ℚ := [")) return false;
  for (std::uint8_t i = 0; i < surface.sample_count; ++i) {
    if (i != 0 && !out.text(",")) return false;
    if (!rational(out,surface.source[i])) return false;
  }
  if (!out.text("]\n\ndef heldoutOrganPredictions : List ℚ := [")) return false;
  for (std::uint8_t i = 0; i < surface.sample_count; ++i) {
    if (i != 0 && !out.text(",")) return false;
    if (!rational(out,surface.predicted[i])) return false;
  }
  if (!out.text("]\n\ndef heldoutRecurrenceStatement : Prop :=\n  ")) return false;
  for (std::uint8_t n = 0; n + 2U < surface.sample_count; ++n) {
    if (n != 0 && !out.text(" ∧\n  ")) return false;
    for (std::uint8_t shift = 0; shift < 3; ++shift) {
      if (shift != 0 && !out.text(" + ")) return false;
      if (!out.integer(surface.organ.coefficients[shift]) || !out.text(" * ") ||
          !rational(out,surface.predicted[n+shift])) return false;
    }
    if (!out.text(" = 0")) return false;
  }
  return out.text("\n\ntheorem heldoutHolonomyOrganImprovement :\n"
      "    selfHolonomyKernel = [1,-3,1] ∧\n"
      "    heldoutTriangleTrace = heldoutOrganPredictions ∧ heldoutRecurrenceStatement := by\n"
      "  norm_num [selfHolonomyKernel, heldoutTriangleTrace, heldoutOrganPredictions,\n"
      "    heldoutRecurrenceStatement]\n\n"
      "theorem generated_heldout_holonomy_transport :\n"
      "    selfHolonomyKernel = [1,-3,1] ∧\n"
      "    heldoutTriangleTrace = heldoutOrganPredictions ∧ heldoutRecurrenceStatement := by\n"
      "  exact heldoutHolonomyOrganImprovement\n\n"
      "end Soma.Holonics.R32\n\n"
      "#check Soma.Holonics.R32.generated_heldout_holonomy_transport\n");
}

}  // namespace holonics::codec
