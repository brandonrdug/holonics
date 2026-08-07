#pragma once

#include <holonics/codec/trace_fiber_face.hpp>
#include <holonics/codec/rederivation_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool render_trace_fiber_dossier(
    const trace_fiber_discovery_surface &d,
    const heldout_trace_fiber_surface &h,
    trace_fiber_dossier_face &face) noexcept {
  using rederivation_render_detail::writer;
  writer out{face};
  face.identity = exact::word{201'412};
  face.passage = h.passage;
  return d.exact && h.exact &&
         out.text("# R34 three-face trace-fiber return\n\nTruth status: "
                  "project-postulate pending gate admission.\n\nThe three source "
                  "ecologies formed 5,184 ordered transition triples and ") &&
         out.natural(d.group_count) &&
         out.text(" exact lower-fiber archetypes. The discriminant partition "
                  "contains ") &&
         out.natural(d.branch_count) && out.text(" branch rows and ") &&
         out.natural(d.two_sheet_count) &&
         out.text(" two-sheet rows. These are complete bounded counts, not "
                  "probabilities.\n\nTwo independently selected primitive organs transport "
                  "the sum and product of the ordered triple traces from six "
                  "lower trace coordinates. Together they form one monic "
                  "quadratic. Its discriminant is the exact square of the root "
                  "gap: zero joins the sheets, while a positive value retains "
                  "two possible ordered traces.\n\nThe held-out local system exposed "
                  "lower face (") &&
         out.integer(h.lower[0]) && out.text(",") && out.integer(h.lower[1]) &&
         out.text(",") && out.integer(h.lower[2]) && out.text(",") &&
         out.integer(h.lower[3]) && out.text(",") && out.integer(h.lower[4]) &&
         out.text(",") && out.integer(h.lower[5]) && out.text(") and oriented anchor ") &&
         out.integer(h.anchor) && out.text(". The organs returned roots ") &&
         out.integer(h.roots[0]) && out.text(" and ") && out.integer(h.roots[1]) &&
         out.text(", then predicted hidden companion ") && out.integer(h.companion) &&
         out.text(" before comparison; the source return agreed. Without "
                  "orientation the same unordered roots remain, but neither is "
                  "named as the companion.\n\nThe lower receiver therefore lifts to "
                  "a finite algebraic fiber, not to a complete matrix geometry. "
                  "Matrix entries, source lineage, rechart and ordered-sheet "
                  "assignment remain outside it. Higher rank, arbitrary character "
                  "varieties, Hodge realization, RH and autonomous theorem "
                  "valuation remain outside this aperture.\n");
}

} // namespace holonics::codec
