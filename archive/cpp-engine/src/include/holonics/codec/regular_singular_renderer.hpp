#pragma once

#include <holonics/codec/regular_singular_face.hpp>

namespace holonics::codec {
namespace regular_singular_render_detail {

HOLONICS_CALLABLE constexpr bool proof(regular_singular_face& out) noexcept {
  return append_regular_singular(out.bytes, out.byte_count,
      "import Mathlib.LinearAlgebra.Matrix.Notation\nimport Mathlib.Tactic.Ring\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.FieldSimp\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "open Matrix\nnamespace Soma.Holonics.R20\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def residueZero : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, -1]\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def residueOne : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; -1, -1]\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def residueInfinity : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 2]\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "theorem generated_residue_algebra :\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    residueInfinity = -(residueZero + residueOne) ∧\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    (residueInfinity - 1) * (residueInfinity - 1) = 0 := by\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "  native_decide\n\ndef zeroCoefficient (n : ℕ) : ℚ := 1 / (n + 1)\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "theorem generated_zero_frobenius_step (n : ℕ) :\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    ((n : ℚ) + 1) * ((n : ℚ) + 2) * zeroCoefficient (n + 1) =\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "      ((n : ℚ) + 1) ^ 2 * zeroCoefficient n := by\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "  simp [zeroCoefficient]\n  field_simp\n  ring\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def oneCoefficient (_n : ℕ) : ℚ := 1\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "theorem generated_one_frobenius_step (n : ℕ) :\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    ((n : ℚ) + 1) ^ 2 * (oneCoefficient (n + 1) - oneCoefficient n) = 0 := by\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "  simp [oneCoefficient]\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def oneResonantVector : Fin 2 → ℤ := ![0, 1]\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def oneResonantSource : Fin 2 → ℤ := ![1, -1]\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def oneCokernel : Fin 2 → ℤ := ![1, 0]\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "theorem generated_resonance_obstruction :\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    residueZero *ᵥ oneResonantVector = oneResonantSource ∧\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    dotProduct oneCokernel oneResonantSource = 1 := by\n  native_decide\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def monodromyZero : Matrix (Fin 2) (Fin 2) ℤ := 1\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def monodromyOne (omega : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, -omega; 0, 1]\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def monodromyInfinity (omega : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, omega; 0, 1]\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def chamberSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "def zeroBasisLoop (omega : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -omega, 1]\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "theorem generated_connection_and_loop (omega : ℤ) :\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    monodromyZero * monodromyOne omega * monodromyInfinity omega = 1 ∧\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    chamberSwap * monodromyOne omega * chamberSwap = zeroBasisLoop omega := by\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "    simp [monodromyZero, monodromyOne, monodromyInfinity, chamberSwap, zeroBasisLoop]\n\n") &&
      append_regular_singular(out.bytes, out.byte_count,
      "end Soma.Holonics.R20\n\n#check Soma.Holonics.R20.generated_connection_and_loop\n");
}

}  // namespace regular_singular_render_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_regular_singular_theory(
    const regular_singular_surface& surface, regular_singular_face& output) noexcept {
  if (surface.passage.value() == 0 || !surface.residue_algebra ||
      !surface.frobenius_steps || !surface.resonance_obstruction ||
      !surface.chamber_connection || !surface.loop_product ||
      !surface.lineage_retained) { return false; }
  output.identity = exact::word{125'400};
  output.passage = surface.passage;
  return regular_singular_render_detail::proof(output);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_regular_singular_explanation(
    const regular_singular_surface& surface,
    regular_singular_explanation& output) noexcept {
  if (surface.passage.value() == 0 || !surface.lineage_retained) { return false; }
  output.identity = exact::word{125'401};
  output.passage = surface.passage;
  return append_regular_singular(output.bytes, output.byte_count,
      "The mounted Gauss equation derives a rank-two Fuchsian current with residues A0, A1, ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "and Ainf=-A0-A1; none was supplied as an expected matrix. The zero and one residues ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "both have eigenvalues -1 and 0, so an integral gap alone cannot decide whether a ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "logarithmic channel opens. At zero the resonant source is the zero vector and lies in ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "the recurrence image. At one the transported source is (1,-1); its pairing with the ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "cokernel vector (1,0) is exactly 1. That nonzero causal component is the obstruction ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "which founds the logarithmic companion. Infinity instead has repeated eigenvalue 1 ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "with a rank-one nilpotent direction. On the declared overlap, the zero and one bases ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "are related by an exact swap. A positive loop adds one formal period omega to the log ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "generator, returning integer-unipotent coefficient matrices over the period carrier. ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "The ordered zero, one, and infinity loop product is identity, while the regular line is ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "the shared eigenvector and the logarithmic direction is generalized. Discriminant, ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "eigenvalue gap, recurrence obstruction, and nilpotent rank are therefore different ") &&
      append_regular_singular(output.bytes, output.byte_count,
      "receivers of the same transported differential geometry.\n");
}

}  // namespace holonics::codec
