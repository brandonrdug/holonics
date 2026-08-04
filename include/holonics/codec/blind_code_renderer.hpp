#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {
namespace blind_code_render_detail {

template<std::size_t Count>
HOLONICS_CALLABLE constexpr bool vector(blind_code_face& out,
    const std::int64_t (&values)[Count], std::size_t used) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "![")) { return false; }
  for (std::size_t slot = 0; slot < used; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, ",")) { return false; }
    if (!append_blind_integer(out.bytes, out.byte_count, values[slot])) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, "]");
}

HOLONICS_CALLABLE constexpr bool matrix(blind_code_face& out,
    const std::int16_t values[blind_code_cell_capacity]
        [blind_code_cell_capacity], std::size_t used) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "![")) { return false; }
  for (std::size_t row = 0; row < used; ++row) {
    if (row != 0 && !append_blind(out.bytes, out.byte_count, ",\n  ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "![")) { return false; }
    for (std::size_t column = 0; column < used; ++column) {
      if (column != 0 && !append_blind(out.bytes, out.byte_count, ",")) { return false; }
      if (!append_blind_integer(out.bytes, out.byte_count, values[row][column])) { return false; }
    }
    if (!append_blind(out.bytes, out.byte_count, "]")) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, "]");
}

HOLONICS_CALLABLE constexpr bool krawtchouk(blind_code_face& out,
    const blind_code_surface& surface) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "![")) { return false; }
  for (std::size_t row = 0; row < blind_code_degree_capacity; ++row) {
    if (row != 0 && !append_blind(out.bytes, out.byte_count, ",\n  ")) { return false; }
    if (!vector(out, surface.krawtchouk[row], blind_code_degree_capacity)) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, "]");
}

HOLONICS_CALLABLE constexpr bool proof(const blind_code_surface& surface,
    blind_code_face& out) noexcept {
  return append_blind(out.bytes, out.byte_count,
      "import Mathlib.LinearAlgebra.Matrix.Notation\nimport Mathlib.Tactic.NormNum\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "open Matrix BigOperators\nnamespace Soma.Holonics.R21.Code\n\n") &&
      append_blind(out.bytes, out.byte_count, "def pairMass : Fin 20 → ℤ := ") &&
      vector(out, surface.mass, surface.cell_count) &&
      append_blind(out.bytes, out.byte_count, "\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "def pairQ : Matrix (Fin 20) (Fin 20) ℤ :=\n  ") &&
      matrix(out, surface.quotient, surface.cell_count) &&
      append_blind(out.bytes, out.byte_count, "\n\n") &&
      append_blind(out.bytes, out.byte_count, "def pairVector : Fin 20 → ℤ := ") &&
      vector(out, surface.witness, surface.cell_count) &&
      append_blind(out.bytes, out.byte_count, "\ndef pairEigenvalue : ℤ := ") &&
      append_blind_integer(out.bytes, out.byte_count, surface.eigenvalue) &&
      append_blind(out.bytes, out.byte_count,
      "\n\ntheorem generated_pair_detailed_balance :\n") &&
      append_blind(out.bytes, out.byte_count,
      "    ∀ i j, pairMass i * pairQ i j = pairMass j * pairQ j i := by\n  native_decide\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "theorem generated_tensor_jacobi_eigenvector :\n") &&
      append_blind(out.bytes, out.byte_count,
      "    pairQ *ᵥ pairVector = pairEigenvalue • pairVector := by\n  native_decide\n\n") &&
      append_blind(out.bytes, out.byte_count, "def codeWeight : Fin 8 → ℤ := ") &&
      vector(out, surface.weight, blind_code_degree_capacity) &&
      append_blind(out.bytes, out.byte_count, "\ndef codeDual : Fin 8 → ℤ := ") &&
      vector(out, surface.dual, blind_code_degree_capacity) &&
      append_blind(out.bytes, out.byte_count,
      "\ndef krawtchouk : Matrix (Fin 8) (Fin 8) ℤ :=\n  ") &&
      krawtchouk(out, surface) &&
      append_blind(out.bytes, out.byte_count,
      "\n\ntheorem generated_code_moment_transport :\n") &&
      append_blind(out.bytes, out.byte_count,
      "    ∀ j, codeDual j * 16 = ∑ i, codeWeight i * krawtchouk j i := by\n  native_decide\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "def characteristicMultiplicity : Fin 8 → ℤ := ") &&
      vector(out, surface.multiplicity, blind_code_degree_capacity) &&
      append_blind(out.bytes, out.byte_count,
      "\n\ntheorem generated_pair_characteristic_degree :\n") &&
      append_blind(out.bytes, out.byte_count,
      "    ∑ i, characteristicMultiplicity i = 20 := by\n  native_decide\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "end Soma.Holonics.R21.Code\n\n#check Soma.Holonics.R21.Code.generated_tensor_jacobi_eigenvector\n");
}

}  // namespace blind_code_render_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_blind_code(
    const blind_code_surface& surface, blind_code_face& output) noexcept {
  if (surface.passage.value() == 0 || !surface.incidence || !surface.characteristic ||
      !surface.alternatives || !surface.source_separated || surface.cell_count != 20) {
    return false;
  }
  output.identity = exact::word{126'500};
  output.passage = surface.passage;
  return blind_code_render_detail::proof(surface, output);
}

}  // namespace holonics::codec
