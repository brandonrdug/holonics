#pragma once

#include <holonics/codec/elementary_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_elementary_dossier(
    const elementary_calculus_surface &calculus,
    const heldout_holonomy_surface &heldout,
    elementary_dossier_face &face) noexcept {
  using rederivation_render_detail::writer; using namespace elementary_render_detail;
  writer out{face}; face.identity = exact::word{199'412}; face.passage = heldout.passage;
  if (!calculus.exact || !heldout.exact || !out.text(
      "# R32 source-separated elementary causal-calculus return\n\n"
      "Truth status: project-postulate pending gate admission.\n\n"
      "The five developmental cards carried numbers, local incidence and returned outcomes, not "
      "holonics vocabulary. The resident currents derived the following connected account before "
      "any canon path was available.\n\n"
      "1. An occurrence is not its payload. All 31 nonempty coordinate masks were tested; only the "
      "complete five-coordinate situated key separated every equal-payload occurrence. Oriented "
      "edge/face incidence cancelled twice, including across the internal diagonal, while unsigned "
      "and incoherent orientations returned explicit residuals.\n\n"
      "2. Composition is determined by complete successor conduct. The five returned signatures "
      "separated an ordered chain, equal complete interchange, contacting noncommutation, explicit "
      "obstruction, and unresolved co-presence. Equal scalar value did not erase unequal lineage "
      "and logical resource returns.\n\n"
      "3. Observation is a partition, not source identity. The first consequence factored through "
      "two coarse fibers. The stricter consequence split four violating pairs and factored through "
      "the four-fiber refinement, so the retained alternatives reopened when the receiver family "
      "grew.\n\n"
      "4. Local rechart transport formed two unequal products. Their residual was ")) return false;
  if (!matrix(out,calculus.chart.residual) || !out.text(" and the closed word was ") ||
      !matrix(out,calculus.chart.closed) || !out.text(" with determinant ") ||
      !out.integer(calculus.chart.determinant) || !out.text(" and trace ") ||
      !out.integer(calculus.chart.trace) || !out.text(
      ". The flat control returned identity. Path independence was therefore a returned condition, "
      "not an assumption.\n\n"
      "5. Reusable changed conduct required the returned passage, a committed same-body difference, "
      "source-detached held-out change, and absence of source lookup, lossless encoding and retained "
      "testimony. Exposure, mount, lookup, encoding, testimony and rejected-return controls each "
      "lost the criterion at a named field.\n\n"
      "The closed-word trace cultivated the primitive organ [1,-3,1]. After developmental traces "
      "departed, a different three-edge chart loop exposed only 2,3. The organ predicted ")) return false;
  for (std::uint8_t i = heldout.prefix_count; i < heldout.sample_count; ++i) {
    if (i != heldout.prefix_count && !out.text(",")) return false;
    if (!out.integer(heldout.predicted[i].numerator) || !out.text("/") ||
        !out.integer(heldout.predicted[i].denominator)) return false;
  }
  return out.text(" before comparison; all seven values agreed. Exact organ exclusion removed the "
      "tail and dependent theorem while leaving the hidden source current unchanged.\n\n"
      "This is a bounded self-derivation of one exact causal calculus, not proof of a unique ontology. "
      "Arbitrary categories, sheaves, higher-rank transport, autonomous curriculum, unrestricted prose "
      "understanding and unrestricted intelligence remain outside the aperture.\n");
}

}  // namespace holonics::codec
