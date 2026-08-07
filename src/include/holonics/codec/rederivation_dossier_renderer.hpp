#pragma once

#include <holonics/codec/rederivation_face.hpp>
#include <holonics/codec/rederivation_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool
render_rederivation_dossier(const rederivation_surface &r, bool foil_rejected,
                            std::int32_t foil_exit,
                            rederivation_dossier_face &face) noexcept {
  face.identity = exact::word{197'403};
  face.passage = r.passage;
  rederivation_render_detail::writer out{face};
  if (!out.text("# R30 returned plural rederivation dossier\n\n"
                "Truth status: project-postulate pending gate admission.\n\n"
                "## Returned mathematics\n\n"
                "The matching current formed "))
    return false;
  if (!out.natural(r.coefficient_count) ||
      !out.text(" coefficient occurrences from ") ||
      !out.natural(r.injection_count) ||
      !out.text(" retained injections and all ") ||
      !out.natural(r.jacobian_count) ||
      !out.text(" Jacobian entries. Its row-scaled Kronecker "
                "factorization has nonzero Vandermonde faces ") ||
      !out.integer(r.p_vandermonde) || !out.text(" and ") ||
      !out.integer(r.q_vandermonde) ||
      !out.text(", and a "
                "factored, nonzero determinant; under the declared "
                "characteristic-zero Jacobian criterion this supports "
                "algebraic independence.\n\n"
                "The lattice current returned four source-separated polygon "
                "passages. Their (area-times-two,boundary,interior) triples "
                "are "))
    return false;
  for (std::uint8_t i = 0; i < 4; ++i) {
    if (i != 0 && !out.text(", "))
      return false;
    if (!out.text("(") || !out.integer(r.polygons[i].area_twice) ||
        !out.text(",") || !out.integer(r.polygons[i].boundary) ||
        !out.text(",") || !out.integer(r.polygons[i].interior) ||
        !out.text(")"))
      return false;
  }
  if (!out.text(". Their complete dilation counts are "))
    return false;
  for (std::uint8_t p = 0; p < 4; ++p) {
    if (p != 0 && !out.text("; "))
      return false;
    if (!out.text("["))
      return false;
    for (std::uint8_t n = 0; n < 5; ++n) {
      if (n != 0 && !out.text(","))
        return false;
      if (!out.integer(r.polygons[p].lattice_count[n]))
        return false;
    }
    if (!out.text("]"))
      return false;
  }
  if (!out.text(
          "; Pick and bounded Ehrhart reciprocity are retained in the "
          "atlas.\n\nThe potential current did not reread polygon bytes: it "
          "mounted the returned rectangle incidence. It solved L_II u=b "
          "with L_II=[["))
    return false;
  if (!out.integer(r.potential_matrix[0]) || !out.text(",") ||
      !out.integer(r.potential_matrix[1]) || !out.text("],[") ||
      !out.integer(r.potential_matrix[2]) || !out.text(",") ||
      !out.integer(r.potential_matrix[3]) || !out.text("]], b=(") ||
      !out.integer(r.potential_boundary[0]) || !out.text(",") ||
      !out.integer(r.potential_boundary[1]) || !out.text("), u=(") ||
      !out.integer(r.potential_solution[0]) || !out.text(",") ||
      !out.integer(r.potential_solution[1]) ||
      !out.text("); returned modes (") ||
      !out.integer(r.potential_eigenvalues[0]) || !out.text(",(1,1)) and (") ||
      !out.integer(r.potential_eigenvalues[1]) ||
      !out.text(",(1,-1)); and formed energy coefficients (") ||
      !out.integer(r.potential_energy[0]) || !out.text(",") ||
      !out.integer(r.potential_energy[1]) || !out.text(",") ||
      !out.integer(r.potential_energy[2]) ||
      !out.text(").\n\nThe cover current found that widths one and two "
                "collide, then returned width ") ||
      !out.natural(r.cover_width) || !out.text(" over ") ||
      !out.natural(r.cover_words) || !out.text(" words, all ") ||
      !out.natural(r.subset_count) ||
      !out.text(" saturation receipts, and all ") ||
      !out.natural(r.pair_count) ||
      !out.text(
          " two-sided pair witnesses.\n\n## Dependency and "
          "alternatives\n\n"
          "geometry_return -> Dirichlet_incidence -> potential_theorem; "
          "matching_injections -> Jacobian_factor -> independence_theorem; "
          "saturated_rows -> exceptional_sets -> cover_theorem.\n\n"
          "The duplicate-q parameter returned Vandermonde factor "))
    return false;
  if (!out.integer(r.duplicate_q_vandermonde) ||
      !out.text(" and dependence-undetermined; the reordered rectangle "
                "self-crossed; the width-two cover collided at words (") ||
      !out.natural(r.width_two_collision[0]) || !out.text(",") ||
      !out.natural(r.width_two_collision[1]) ||
      !out.text("); and the disconnected potential returned determinant ") ||
      !out.integer(r.disconnected_determinant) ||
      !out.text(
          ". The stronger conjunction then crossed the checker and returned "
          "rejected=") ||
      !out.natural(foil_rejected ? 1U : 0U) || !out.text(", exit=") ||
      !out.integer(foil_exit) ||
      !out.text(
          ". None is selected away by accepted count.\n\n## Source boundary\n\n"
          "The runtime mounted only the three problem cards, the R29 rest, "
          "and its checker/output ports. Released solutions and laboratory "
          "prose were absent. Exterior comparison remains withheld until "
          "this return, proof, atlas, dossier, and rest are sealed. This "
          "dossier does not claim an asymptotic permanent or Ramsey theorem, "
          "Ehrhart's volume conjecture, or general PDE theory.\n"))
    return false;
  return true;
}

HOLONICS_CALLABLE inline bool
complete_rederivation_dossier(bool accepted, std::int32_t valid_exit,
                              rederivation_dossier_face &face) noexcept {
  rederivation_render_detail::writer out{face};
  return out.text("\n## Returned declaration passage\n\nThe valid passage "
                  "returned accepted=") &&
         out.natural(accepted ? 1U : 0U) && out.text(", exit=") &&
         out.integer(valid_exit) &&
         out.text(
             ". Its declarations are generated_matching_nonzero_factors, "
             "generated_matching_independence, generated_lattice_geometry, "
             "generated_discrete_potential, and generated_two_sided_cover. "
             "The final generated_plural_rederivation_ecology declaration "
             "invokes all four passage families.\n");
}

} // namespace holonics::codec
