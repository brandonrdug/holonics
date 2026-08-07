#pragma once

#include <holonics/codec/characteristic_face.hpp>

namespace holonics::codec {
namespace characteristic_render_detail {

HOLONICS_CALLABLE constexpr bool prelude(characteristic_face& out) noexcept {
  return append_characteristic(out.bytes, out.byte_count,
      "import Mathlib.Data.Nat.GCD.Basic\nimport Mathlib.Algebra.Polynomial.Monic\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "import Mathlib.Algebra.Polynomial.Degree.Operations\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "import Mathlib.LinearAlgebra.Matrix.Notation\nimport Mathlib.Tactic.Ring\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\n\nopen Polynomial Matrix\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "namespace Soma.Holonics.R19\n\n");
}

HOLONICS_CALLABLE constexpr bool diagonal(characteristic_face& out) noexcept {
  return append_characteristic(out.bytes, out.byte_count,
      "noncomputable def diagonalCharacteristic (m n : Nat) : Polynomial ℤ :=\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  (X ^ Nat.lcm m n - 1) ^ Nat.gcd m n\n\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "theorem generated_diagonal_characteristic_degree (m n : Nat)\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "    (hm : m ≠ 0) (hn : n ≠ 0) :\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "    (diagonalCharacteristic m n).natDegree = m * n := by\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  unfold diagonalCharacteristic\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  change ((X ^ Nat.lcm m n - C (1 : ℤ)) ^ Nat.gcd m n).natDegree = m * n\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  rw [(monic_X_pow_sub_C (1 : ℤ) (Nat.lcm_ne_zero hm hn)).natDegree_pow]\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  rw [natDegree_X_pow_sub_C, Nat.gcd_mul_lcm]\n\n");
}

HOLONICS_CALLABLE constexpr bool weighted(characteristic_face& out) noexcept {
  return append_characteristic(out.bytes, out.byte_count,
      "def weightedTwoCycle (u v : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  !![0, v; u, 0]\n\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "theorem generated_weighted_two_cycle (u v : ℤ) :\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "    (weightedTwoCycle u v).charpoly = X ^ 2 - C (u * v) := by\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  rw [Matrix.charpoly_fin_two]\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  simp [weightedTwoCycle, Matrix.trace, Matrix.det_fin_two]\n  ring\n\n");
}

HOLONICS_CALLABLE constexpr bool rechart(characteristic_face& out) noexcept {
  return append_characteristic(out.bytes, out.byte_count,
      "def sourceReturn : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "def rechart : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "def rechartInv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]\n\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "theorem generated_rechart_characteristic :\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "    (rechart * sourceReturn * rechartInv).charpoly = sourceReturn.charpoly := by\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  simp [Matrix.charpoly_fin_two, sourceReturn, rechart, rechartInv, Matrix.trace]\n\n");
}

HOLONICS_CALLABLE constexpr bool indicial(characteristic_face& out) noexcept {
  return append_characteristic(out.bytes, out.byte_count,
      "def gaussZeroIndicial (rho : ℚ) := rho * (rho - 1) + 2 * rho\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "def gaussOneIndicial (rho : ℚ) := rho * (rho + 1 + 1 - 2)\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "def gaussInfinityIndicial (rho : ℚ) := (rho - 1) * (rho - 1)\n\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "theorem generated_gauss_indicial (rho : ℚ) :\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "    gaussZeroIndicial rho = rho * (rho + 1) ∧\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "    gaussOneIndicial rho = rho ^ 2 ∧\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "    gaussInfinityIndicial rho = (rho - 1) ^ 2 := by\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  constructor\n  · simp [gaussZeroIndicial]\n    ring\n  constructor\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  · simp [gaussOneIndicial]\n    ring\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "  · simp [gaussInfinityIndicial, pow_two]\n\nend Soma.Holonics.R19\n\n") &&
      append_characteristic(out.bytes, out.byte_count,
      "#check Soma.Holonics.R19.generated_diagonal_characteristic_degree\n");
}

}  // namespace characteristic_render_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_characteristic_theory(
    const characteristic_surface& surface, characteristic_face& output) noexcept {
  if (surface.passage.value() == 0 || !surface.diagonal_factor ||
      !surface.weighted_cycle || !surface.matrix_controls ||
      !surface.discriminants_typed || !surface.gauss_indicial ||
      !surface.lineage_retained) { return false; }
  output.identity = exact::word{124'400};
  output.passage = surface.passage;
  return characteristic_render_detail::prelude(output) &&
      characteristic_render_detail::diagonal(output) &&
      characteristic_render_detail::weighted(output) &&
      characteristic_render_detail::rechart(output) &&
      characteristic_render_detail::indicial(output);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_characteristic_explanation(
    const characteristic_surface& surface, characteristic_explanation& output) noexcept {
  if (surface.passage.value() == 0 || !surface.lineage_retained) { return false; }
  output.identity = exact::word{124'401};
  output.passage = surface.passage;
  return append_characteristic(output.bytes, output.byte_count,
      "The diagonal phase current is an exact permutation with gcd(m,n) tours of ") &&
      append_characteristic(output.bytes, output.byte_count,
      "lcm(m,n) steps. Its characteristic factor is X^lcm-1, repeated once per tour, ") &&
      append_characteristic(output.bytes, output.byte_count,
      "while its minimal factor is not repeated. Shared-factor multiplicity therefore records ") &&
      append_characteristic(output.bytes, output.byte_count,
      "coincident independent lineages rather than a singular local cell. Each exact shape type ") &&
      append_characteristic(output.bytes, output.byte_count,
      "is retained as a formal transport indeterminate; its exponent around a tour is the shape ") &&
      append_characteristic(output.bytes, output.byte_count,
      "population seen by any later constitutive specialization. Scalar edge weights return only ") &&
      append_characteristic(output.bytes, output.byte_count,
      "their ordered product in the characteristic factor, so equal spectra can forget unequal ") &&
      append_characteristic(output.bytes, output.byte_count,
      "edge words. Rank-two controls show both that edge order can change the characteristic ") &&
      append_characteristic(output.bytes, output.byte_count,
      "return and that a conjugate rechart preserves it. Identity and Jordan returns have the ") &&
      append_characteristic(output.bytes, output.byte_count,
      "same characteristic polynomial but different fixed-current dimensions. Finally, the ") &&
      append_characteristic(output.bytes, output.byte_count,
      "Gauss (1,1;2) differential operator has exponent pairs (0,-1), (0,0), and (1,1) at ") &&
      append_characteristic(output.bytes, output.byte_count,
      "zero, one, and infinity; the repeated exponent at one leaves a logarithmic/unipotent ") &&
      append_characteristic(output.bytes, output.byte_count,
      "alternative which the single R18 coefficient branch could not expose.\n");
}

}  // namespace holonics::codec
