#pragma once

#include <holonics/codec/rederivation_cover_renderer.hpp>
#include <holonics/codec/rederivation_face.hpp>
#include <holonics/codec/rederivation_matching_renderer.hpp>
#include <holonics/codec/rederivation_renderer_atoms.hpp>

namespace holonics::codec {

HOLONICS_CALLABLE inline bool
render_rederivation(const rederivation_surface &source,
                    rederivation_formal_face &face) noexcept {
  using rederivation_render_detail::writer;
  writer out{face};
  face.identity = exact::word{197'401};
  face.passage = source.passage;
  if (!source.all_exact || source.coefficient_count != 49 ||
      source.jacobian_count != rederivation_surface_jacobians ||
      source.pair_count != rederivation_surface_pairs)
    return false;
  if (!out.text("import Mathlib.Tactic.NormNum\n"
                "import Mathlib.Tactic.IntervalCases\n"
                "import Mathlib.Tactic.Ring\n"
                "import Mathlib.Tactic.Positivity\n\nnamespace "
                "Soma.Holonics.R30\n\n"))
    return false;
  if (!rederivation_matching_render_detail::render(source, out) ||
      !out.text("def polygonStatement : Prop :=\n  "))
    return false;
  bool first = true;
  for (const auto &p : source.polygons) {
    if (!first && !out.text(" ∧\n  "))
      return false;
    first = false;
    if (!out.text("((") || !out.integer(p.area_twice) ||
        !out.text(" : ℤ) = 2 * ") || !out.integer(p.interior) ||
        !out.text(" + ") || !out.integer(p.boundary) || !out.text(" - 2)"))
      return false;
    for (std::uint8_t n = 0; n < 5; ++n) {
      if (!out.text(" ∧ ((2 * ") || !out.integer(p.lattice_count[n]) ||
          !out.text(" : ℤ) = ") || !out.integer(p.area_twice) ||
          !out.text(" * ") || !out.natural(n) || !out.text("^2 + ") ||
          !out.integer(p.boundary) || !out.text(" * ") || !out.natural(n) ||
          !out.text(" + 2)"))
        return false;
    }
    for (std::uint8_t n = 1; n < 5; ++n) {
      if (!out.text(" ∧ ((2 * ") || !out.integer(p.reciprocal_interior[n]) ||
          !out.text(" : ℤ) = ") || !out.integer(p.area_twice) ||
          !out.text(" * ") || !out.natural(n) || !out.text("^2 - ") ||
          !out.integer(p.boundary) || !out.text(" * ") || !out.natural(n) ||
          !out.text(" + 2)"))
        return false;
    }
  }
  if (!out.text(
          "\n\ntheorem generated_lattice_geometry : polygonStatement := by\n"
          "  unfold polygonStatement\n  norm_num\n\ndef potentialStatement : "
          "Prop :=\n  ((") ||
      !out.integer(source.potential_matrix[0]) || !out.text("*") ||
      !out.integer(source.potential_solution[0]) || !out.text(" + ") ||
      !out.integer(source.potential_matrix[1]) || !out.text("*") ||
      !out.integer(source.potential_solution[1]) || !out.text(" : ℤ) = ") ||
      !out.integer(source.potential_boundary[0]) || !out.text(") ∧ ((") ||
      !out.integer(source.potential_matrix[2]) || !out.text("*") ||
      !out.integer(source.potential_solution[0]) || !out.text(" + ") ||
      !out.integer(source.potential_matrix[3]) || !out.text("*") ||
      !out.integer(source.potential_solution[1]) || !out.text(" : ℤ) = ") ||
      !out.integer(source.potential_boundary[1]) ||
      !out.text(") ∧\n  (∀ X : ℤ, ") ||
      !out.integer(source.potential_characteristic[0]) ||
      !out.text("*X^2 + ") ||
      !out.integer(source.potential_characteristic[1]) || !out.text("*X + ") ||
      !out.integer(source.potential_characteristic[2]) || !out.text(" = (X-") ||
      !out.integer(source.potential_eigenvalues[0]) || !out.text(")*(X-") ||
      !out.integer(source.potential_eigenvalues[1]) ||
      !out.text(") ) ∧\n  ((") || !out.integer(source.potential_matrix[0]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[0]) ||
      !out.text(" + ") || !out.integer(source.potential_matrix[1]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[1]) ||
      !out.text(" : ℤ) = ") || !out.integer(source.potential_eigenvalues[0]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[0]) ||
      !out.text(") ∧ ((") || !out.integer(source.potential_matrix[2]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[0]) ||
      !out.text(" + ") || !out.integer(source.potential_matrix[3]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[1]) ||
      !out.text(" : ℤ) = ") || !out.integer(source.potential_eigenvalues[0]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[1]) ||
      !out.text(") ∧\n  ((") || !out.integer(source.potential_matrix[0]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[2]) ||
      !out.text(" + ") || !out.integer(source.potential_matrix[1]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[3]) ||
      !out.text(" : ℤ) = ") || !out.integer(source.potential_eigenvalues[1]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[2]) ||
      !out.text(") ∧ ((") || !out.integer(source.potential_matrix[2]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[2]) ||
      !out.text(" + ") || !out.integer(source.potential_matrix[3]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[3]) ||
      !out.text(" : ℤ) = ") || !out.integer(source.potential_eigenvalues[1]) ||
      !out.text("*") || !out.integer(source.potential_eigenvectors[3]) ||
      !out.text(") ∧\n  (∀ r s : ℤ, ") ||
      !out.integer(source.potential_energy[0]) || !out.text("*r^2 + ") ||
      !out.integer(source.potential_energy[1]) || !out.text("*r*s + ") ||
      !out.integer(source.potential_energy[2]) || !out.text("*s^2 = ") ||
      !out.integer(source.potential_eigenvalues[0]) || !out.text("*r^2 + ") ||
      !out.integer(source.potential_eigenvalues[0]) ||
      !out.text("*s^2 + (r-s)^2) ∧\n  (∀ r s : ℤ, 0 ≤ ") ||
      !out.integer(source.potential_eigenvalues[0]) || !out.text("*r^2 + ") ||
      !out.integer(source.potential_eigenvalues[0]) ||
      !out.text(
          "*s^2 + (r-s)^2)\n\ntheorem generated_discrete_potential : "
          "potentialStatement := by\n  unfold potentialStatement\n  "
          "constructor\n"
          "  · norm_num\n  constructor\n  · norm_num\n  constructor\n"
          "  · intro X; ring\n  constructor\n  · norm_num\n  constructor\n"
          "  · norm_num\n  constructor\n  · norm_num\n  constructor\n  · "
          "norm_num\n  constructor\n  · intro r s; ring\n"
          "  · intro r s; positivity\n\n"))
    return false;
  if (!rederivation_cover_render_detail::render(source, out))
    return false;
  return out.text(
      "theorem "
      "generated_plural_rederivation_ecology :\n"
      "    matchingStatement ∧ polygonStatement ∧ potentialStatement ∧ "
      "coverStatement := by\n"
      "  exact ⟨generated_matching_independence, generated_lattice_geometry,\n"
      "    generated_discrete_potential, generated_two_sided_cover⟩\n\nend "
      "Soma.Holonics.R30\n\n#check "
      "Soma.Holonics.R30.generated_plural_rederivation_ecology\n");
}

HOLONICS_CALLABLE inline bool
render_rederivation_foil(exact::word passage,
                         std::int64_t duplicate_q_vandermonde,
                         std::uint8_t words, std::uint8_t maximum_width,
                         rederivation_foil_face &face) noexcept {
  face.identity = exact::word{197'402};
  face.passage = passage;
  rederivation_render_detail::writer out{face};
  return out.text("import Mathlib.Tactic.NormNum\nnamespace "
                  "Soma.Holonics.R30\n"
                  "theorem rejected_duplicate_and_short_cover_foil : ((") &&
         out.integer(duplicate_q_vandermonde) && out.text(" : ℤ) ≠ 0) ∧ ((") &&
         out.natural(words) && out.text(" : ℕ) ≤ 2^") &&
         out.natural(static_cast<std::uint64_t>(maximum_width - 1U)) &&
         out.text(") := by constructor <;> norm_num\nend Soma.Holonics.R30\n");
}

} // namespace holonics::codec
