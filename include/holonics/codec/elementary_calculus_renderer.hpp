#pragma once

#include <holonics/codec/elementary_renderer_foundations.hpp>
#include <holonics/codec/elementary_renderer_geometry.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_elementary_calculus(
    const elementary_calculus_surface &surface, elementary_formal_face &face) noexcept {
  using rederivation_render_detail::writer; using namespace elementary_render_detail;
  writer out{face}; face.identity = exact::word{199'410}; face.passage = surface.passage;
  if (!surface.exact || !out.text(
      "import Mathlib.LinearAlgebra.Matrix.Notation\n"
      "import Mathlib.Tactic.NormNum\n\n"
      "open Matrix\n\n"
      "namespace Soma.Holonics.R32\n\n")) return false;
  if (!render_occurrence(out,surface.occurrence) ||
      !render_composition(out,surface.composition) ||
      !render_receiver(out,surface.receiver) ||
      !render_chart(out,surface.chart) ||
      !render_conduct(out,surface.conduct) ||
      !render_self_organ(out,surface.organ)) return false;
  return out.text(
      "theorem generated_elementary_causal_calculus :\n"
      "    List.Nodup [occurrence0,occurrence1,occurrence2,occurrence3,occurrence4,occurrence5] ∧\n"
      "    signedBoundaryStatement ∧ compositionStatement ∧ receiverStatement ∧\n"
      "    localChartStatement ∧ returnedConductStatement ∧ selfHolonomyRecurrenceStatement := by\n"
      "  exact ⟨occurrenceIdentity, orientedBoundaryCancellation, fiveCompositionArchetypes,\n"
      "    receiverReturn, localChartTransport, returnedConductCriterion, selfHolonomyOrganReturn⟩\n\n"
      "end Soma.Holonics.R32\n\n"
      "#check Soma.Holonics.R32.generated_elementary_causal_calculus\n");
}

}  // namespace holonics::codec
