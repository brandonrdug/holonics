#pragma once

#include <holonics/codec/phase_crystal_face.hpp>

namespace holonics::codec {
namespace phase_crystal_render_detail {

HOLONICS_CALLABLE constexpr bool prelude(phase_crystal_face& out) noexcept {
  return append_phase_crystal(out.bytes, out.byte_count,
      "import Mathlib.Data.Nat.GCD.Basic\nimport Mathlib.Data.Finset.Prod\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "import Mathlib.Data.Rat.Defs\nimport Mathlib.Tactic.FieldSimp\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\n\nnamespace Soma.Holonics.R18\n\n");
}

HOLONICS_CALLABLE constexpr bool diagonal(phase_crystal_face& out) noexcept {
  return append_phase_crystal(out.bytes, out.byte_count,
      "theorem generated_diagonal_return (m n k : Nat) :\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "    (k % m = 0 ∧ k % n = 0) ↔ Nat.lcm m n ∣ k := by\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  simp only [← Nat.dvd_iff_mod_eq_zero, Nat.lcm_dvd_iff]\n\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "theorem generated_coprime_diagonal_return (m n k : Nat) (h : Nat.Coprime m n) :\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "    (k % m = 0 ∧ k % n = 0) ↔ m * n ∣ k := by\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  rw [generated_diagonal_return, h.lcm_eq_mul]\n\n");
}

HOLONICS_CALLABLE constexpr bool population(phase_crystal_face& out) noexcept {
  return append_phase_crystal(out.bytes, out.byte_count,
      "theorem generated_cell_population_product (first second : Finset Nat) :\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "    (first ×ˢ second).card = first.card * second.card := by\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  exact Finset.card_product first second\n\n");
}

HOLONICS_CALLABLE constexpr bool series(phase_crystal_face& out) noexcept {
  return append_phase_crystal(out.bytes, out.byte_count,
      "def gaussStep112 (n : ℕ) : ℚ :=\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  (((n : ℚ) + 1) * ((n : ℚ) + 1)) /\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "    (((n : ℚ) + 2) * ((n : ℚ) + 1))\n\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "theorem generated_gauss_112_transport (n : ℕ) :\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "    (1 / ((n : ℚ) + 1)) * gaussStep112 n = 1 / ((n : ℚ) + 2) := by\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  simp only [gaussStep112]\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  have h1 : (n : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  have h2 : (n : ℚ) + 2 ≠ 0 := by\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "    exact_mod_cast Nat.succ_ne_zero (n + 1)\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "  field_simp\n\nend Soma.Holonics.R18\n\n") &&
      append_phase_crystal(out.bytes, out.byte_count,
      "#check Soma.Holonics.R18.generated_coprime_diagonal_return\n");
}

}  // namespace phase_crystal_render_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_phase_crystal_theory(
    const phase_crystal_surface& surface, phase_crystal_face& output) noexcept {
  const auto& plan = surface;
  if (plan.passage.value() == 0 || !plan.diagonal_lcm || !plan.coprime_full_tour ||
      !plan.cell_population_product || !plan.seam_cancellation ||
      !plan.gauss_transport || !plan.projection_distinguished) { return false; }
  output.identity = exact::word{124'300};
  output.passage = plan.passage;
  return phase_crystal_render_detail::prelude(output) &&
      phase_crystal_render_detail::diagonal(output) &&
      phase_crystal_render_detail::population(output) &&
      phase_crystal_render_detail::series(output);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_phase_crystal_explanation(
    const phase_crystal_surface& surface, phase_crystal_explanation& output) noexcept {
  if (surface.passage.value() == 0 || !surface.projection_distinguished) {
    return false;
  }
  output.identity = exact::word{124'301};
  output.passage = surface.passage;
  return append_phase_crystal(output.bytes, output.byte_count,
      "The returned object is a four-coordinate product of two exact cyclic conic factors. ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "Its two-dimensional product cells share opposed phase edges, so the complete cellular ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "boundary cancels while every seam remains addressable. Diagonal transport advances both ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "residues at once: its orbit count is gcd(m,n), its orbit length is lcm(m,n), and a ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "coprime pair makes one full tour. Local cell shape is the ordered pair of exact squared ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "factor-side lengths; the population of paired types factors, while diagonal adjacency ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "retains their ordering. The Gauss (1,1;2) coefficient current derives 1/(n+1) along ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "those paths. Convex hulls are receiver faces only: dilation and a common rational turn ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "preserve their exact morphology, dominance changes the quotient, and projected crossings ") &&
      append_phase_crystal(output.bytes, output.byte_count,
      "do not become source contacts.\n");
}

}  // namespace holonics::codec
