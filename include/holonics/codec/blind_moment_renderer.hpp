#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {
namespace blind_moment_render_detail {

HOLONICS_CALLABLE constexpr bool matrix(blind_moment_face& out,
    const std::int64_t values[blind_moment_degree_capacity]
        [blind_moment_degree_capacity], std::size_t used) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "![")) { return false; }
  for (std::size_t row = 0; row < used; ++row) {
    if (row != 0 && !append_blind(out.bytes, out.byte_count, ",")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "![")) { return false; }
    for (std::size_t column = 0; column < used; ++column) {
      if (column != 0 && !append_blind(out.bytes, out.byte_count, ",")) { return false; }
      if (!append_blind_integer(out.bytes, out.byte_count, values[row][column])) { return false; }
    }
    if (!append_blind(out.bytes, out.byte_count, "]")) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, "]");
}

HOLONICS_CALLABLE constexpr bool polynomial(blind_moment_face& out,
    const std::int64_t (&coefficients)[blind_polynomial_capacity],
    std::uint8_t degree) noexcept {
  for (std::uint8_t power = 0; power <= degree; ++power) {
    if (power != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
    if (!append_blind_integer(out.bytes, out.byte_count, coefficients[power]) ||
        !append_blind(out.bytes, out.byte_count, ") * x ^ ") ||
        !append_blind_integer(out.bytes, out.byte_count, power)) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr bool roots(blind_moment_face& out,
    const blind_moment_surface& surface) noexcept {
  for (std::uint8_t slot = 0; slot < surface.root_count; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " ∧ ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "recovered ") ||
        !append_blind_integer(out.bytes, out.byte_count, surface.roots[slot]) ||
        !append_blind(out.bytes, out.byte_count, " = 0")) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr bool proof(const blind_moment_surface& surface,
    blind_moment_face& out) noexcept {
  return append_blind(out.bytes, out.byte_count,
      "import Mathlib.LinearAlgebra.Matrix.Notation\nimport Mathlib.Tactic.NormNum\n") &&
      append_blind(out.bytes, out.byte_count,
      "import Mathlib.Tactic.Ring\n\nopen Matrix\nnamespace Soma.Holonics.R21.Moment\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "def det3 (m : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=\n") &&
      append_blind(out.bytes, out.byte_count,
      "  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1) -\n") &&
      append_blind(out.bytes, out.byte_count,
      "  m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0) +\n") &&
      append_blind(out.bytes, out.byte_count,
      "  m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "def h0 : Matrix (Fin 3) (Fin 3) ℤ := ") &&
      matrix(out, surface.hankel, 3) &&
      append_blind(out.bytes, out.byte_count,
      "\ndef h1 : Matrix (Fin 3) (Fin 3) ℤ := ") &&
      matrix(out, surface.shifted, 3) &&
      append_blind(out.bytes, out.byte_count,
      "\ndef pencil (x : ℤ) : ℤ := det3 (fun i j => x * h0 i j - h1 i j)\n") &&
      append_blind(out.bytes, out.byte_count, "def recovered (x : ℤ) : ℤ := ") &&
      polynomial(out, surface.polynomial, surface.degree) &&
      append_blind(out.bytes, out.byte_count,
      "\n\ntheorem generated_hankel_pencil (x : ℤ) : pencil x = ") &&
      append_blind_integer(out.bytes, out.byte_count, surface.determinant) &&
      append_blind(out.bytes, out.byte_count,
      " * recovered x := by\n  simp [pencil, det3, h0, h1, recovered]\n  ring\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "def cubicDiscriminant (a b c : ℤ) : ℤ :=\n") &&
      append_blind(out.bytes, out.byte_count,
      "  a^2*b^2 - 4*b^3 - 4*a^3*c - 27*c^2 + 18*a*b*c\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "theorem generated_vandermonde_discriminant : det3 h0 = ") &&
      append_blind_integer(out.bytes, out.byte_count, surface.determinant) &&
      append_blind(out.bytes, out.byte_count, " ∧ cubicDiscriminant (") &&
      append_blind_integer(out.bytes, out.byte_count, surface.polynomial[2]) &&
      append_blind(out.bytes, out.byte_count, ") (") &&
      append_blind_integer(out.bytes, out.byte_count, surface.polynomial[1]) &&
      append_blind(out.bytes, out.byte_count, ") (") &&
      append_blind_integer(out.bytes, out.byte_count, surface.polynomial[0]) &&
      append_blind(out.bytes, out.byte_count, ") = ") &&
      append_blind_integer(out.bytes, out.byte_count, surface.discriminant) &&
      append_blind(out.bytes, out.byte_count, " := by\n  native_decide\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "theorem generated_recovered_roots : ") && roots(out, surface) &&
      append_blind(out.bytes, out.byte_count, " := by\n  native_decide\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "def collisionH0 : Matrix (Fin 3) (Fin 3) ℤ := ") &&
      matrix(out, surface.collision, 3) &&
      append_blind(out.bytes, out.byte_count,
      "\n\ntheorem generated_collision_obstruction : det3 collisionH0 = 0 := by\n") &&
      append_blind(out.bytes, out.byte_count,
      "  native_decide\n\nend Soma.Holonics.R21.Moment\n\n") &&
      append_blind(out.bytes, out.byte_count,
      "#check Soma.Holonics.R21.Moment.generated_hankel_pencil\n");
}

}  // namespace blind_moment_render_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_blind_moment(
    const blind_moment_surface& surface, blind_moment_face& output) noexcept {
  if (surface.passage.value() == 0 || !surface.incidence || !surface.characteristic ||
      !surface.obstruction || !surface.alternatives || !surface.source_separated ||
      surface.degree != 3 || surface.root_count != 3) { return false; }
  output.identity = exact::word{126'501};
  output.passage = surface.passage;
  return blind_moment_render_detail::proof(surface, output);
}

}  // namespace holonics::codec
