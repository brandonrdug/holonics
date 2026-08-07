#pragma once

#include <holonics/codec/cultivated_organ_face.hpp>
#include <holonics/codec/cultivation_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_cultivated_dossier(
    const cultivated_application_surface &receipt,
    cultivated_dossier_face &face) noexcept {
  using rederivation_render_detail::writer;
  using cultivation_render_detail::kernel_list;
  writer out{face}; face.identity = exact::word{198'412}; face.passage = receipt.passage;
  if (!out.text("# R31 cultivated mathematical-organ return\n\n"
      "Truth status: project-postulate pending gate admission.\n\n"
      "The resident body remounted four checker-founded coefficient geometries. "
      "No developmental sample array, source card, expected tail, or lookup key crossed "
      "the intermediate-rest port.\n\n")) return false;
  constexpr const char *development[4]{"R18 reciprocal", "R24 central-walk",
      "R29 signed-trace", "R30 polygon-incidence"};
  constexpr const char *heldout[4]{"equal conductance star", "square-lattice closed walk",
      "signed two-vertex carrier", "two-generator graded incidence"};
  for (std::uint8_t family = 0; family < cultivated_surface_family_count; ++family) {
    if (!out.text("- ") || !out.text(development[family]) || !out.text(" -> ") ||
        !kernel_list(out, receipt.kernels[family]) || !out.text("; transported into ") ||
        !out.text(heldout[family]) || !out.text(" with prefix ") ||
        !out.natural(receipt.tails[family].prefix_count) || !out.text(", predicted tail ")) return false;
    for (std::uint8_t i = receipt.tails[family].prefix_count;
         i < receipt.tails[family].sample_count; ++i) {
      if (i != receipt.tails[family].prefix_count && !out.text(",")) return false;
      if (!out.integer(receipt.tails[family].predicted[i].numerator) || !out.text("/") ||
          !out.integer(receipt.tails[family].predicted[i].denominator)) return false;
    }
    if (!out.text(". The changed structure returned heldout_residual; the shortened "
        "prefix returned insufficient_prefix; exact identity exclusion returned organ_absent.\n"))
      return false;
  }
  return out.text("\nThe source currents formed current division, two-dimensional walk incidence, "
      "signed matrix powers, and graded exponent incidence before the comparison barrier. "
      "They were not sequence fixtures written in the developmental grammar. Equal returned "
      "streams therefore retain unequal source lineage. The generated held-out checker declaration "
      "invokes all four returned statements. This bounded deed does not establish unrestricted "
      "recurrence discovery, analytic continuation, autonomous curriculum, or general learning.\n");
}

}  // namespace holonics::codec
