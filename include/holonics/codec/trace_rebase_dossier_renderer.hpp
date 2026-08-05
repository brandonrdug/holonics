#pragma once

#include <holonics/codec/rederivation_renderer_atoms.hpp>
#include <holonics/codec/trace_rebase_face.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_trace_rebase_dossier(
    const trace_rebase_discovery_surface &discovery,
    const heldout_trace_rebase_surface &heldout,
    trace_rebase_dossier_face &face) noexcept {
  using rederivation_render_detail::writer;
  writer out{face};
  face.identity = exact::word{202'412};
  face.passage = heldout.passage;
  if (!discovery.exact || !heldout.exact ||
      !out.text("# R35 trace-character rebase and tangent return\n\n"
                "Truth status: project-postulate pending gate admission.\n\n"
                "The machine formed 1,272 source chart states and all 6,360 elementary "
                "matrix-caused rebase edges. From those edges it derived five complete "
                "seven-coordinate polynomial maps, then differentiated the returned "
                "coefficients rather than receiving Jacobians.\n\n"
                "Across the bounded ecology, the per-move projection transitions "
                "(regular-regular, regular-branch, branch-regular, branch-branch) are:\n"))
    return false;
  for (std::uint8_t move = 0; move < 5; ++move) {
    if (!out.text("- move ") || !out.natural(move) || !out.text(": "))
      return false;
    for (std::uint8_t kind = 0; kind < 4; ++kind) {
      if (kind != 0 && !out.text(","))
        return false;
      if (!out.natural(discovery.transitions[move][kind]))
        return false;
    }
    if (!out.text("\n"))
      return false;
  }
  return out.text(
             "\nThe six-dimensional tangent kernel is transported through each exact "
             "map Jacobian. At a branch-fixed face the projection gains a vertical "
             "direction, and the deck return carries that direction with eigenvalue ") &&
         out.integer(discovery.deck_eigenvalue) &&
         out.text(". This eigenvalue belongs to an endomorphism of one fixed tangent "
                  "fiber; no eigenvalue is assigned to unrelated source and target charts.\n\n"
                  "The held-out path contains ") &&
         out.natural(heldout.path_length) &&
         out.text(" generator deeds. Rested map and lift organs predicted every later "
                  "chart, tangent rank, vertical rank and branch face before the hidden "
                  "matrix path opened; the source path then agreed. The branch divisor "
                  "is a property of the selected six-coordinate projection and can move "
                  "under rebase. These finite transition counts are not probabilities, "
                  "and they do not establish arbitrary character-variety, Hodge, or RH "
                  "claims.\n");
}

} // namespace holonics::codec
