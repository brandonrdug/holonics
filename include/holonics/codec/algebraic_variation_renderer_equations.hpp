#pragma once

#include <holonics/codec/algebraic_variation_renderer_atoms.hpp>

namespace holonics::codec::variation_render_detail {

HOLONICS_CALLABLE constexpr bool connection_denominator(
    const algebraic_variation_surface& surface, variation_formal_face& out) noexcept {
  return integer(out, surface.connection_scale) &&
      append_blind(out.bytes, out.byte_count, "*") &&
      parameter_polynomial(out, surface.connection_pole, 3);
}

template<std::size_t Name, std::size_t Derivative>
HOLONICS_CALLABLE constexpr bool connection_hypothesis(
    const algebraic_variation_surface& surface, variation_formal_face& out,
    std::uint8_t row, const char (&name)[Name],
    const char (&derivative)[Derivative]) noexcept {
  return append_blind(out.bytes, out.byte_count, "    (") &&
      append_blind(out.bytes, out.byte_count, name) &&
      append_blind(out.bytes, out.byte_count, " : ") &&
      connection_denominator(surface, out) &&
      append_blind(out.bytes, out.byte_count, "*") &&
      append_blind(out.bytes, out.byte_count, derivative) &&
      append_blind(out.bytes, out.byte_count, " = ") &&
      affine(out, surface.connection_numerator[row][0]) &&
      append_blind(out.bytes, out.byte_count, "*u + ") &&
      affine(out, surface.connection_numerator[row][1]) &&
      append_blind(out.bytes, out.byte_count, "*v)\n");
}

HOLONICS_CALLABLE constexpr bool derivative_hypothesis(
    const algebraic_variation_surface& surface, variation_formal_face& out) noexcept {
  const std::int64_t pole_derivative[2]{surface.connection_pole[1],
      2 * surface.connection_pole[2]};
  return append_blind(out.bytes, out.byte_count, "    (hd : ") &&
      integer(out, surface.connection_scale) &&
      append_blind(out.bytes, out.byte_count, "*") &&
      parameter_polynomial(out, pole_derivative, 2) &&
      append_blind(out.bytes, out.byte_count, "*du + ") &&
      connection_denominator(surface, out) &&
      append_blind(out.bytes, out.byte_count, "*ddu = ") &&
      integer(out, surface.connection_numerator[0][0][1]) &&
      append_blind(out.bytes, out.byte_count, "*u + ") &&
      affine(out, surface.connection_numerator[0][0]) &&
      append_blind(out.bytes, out.byte_count, "*du + ") &&
      integer(out, surface.connection_numerator[0][1][1]) &&
      append_blind(out.bytes, out.byte_count, "*v + ") &&
      affine(out, surface.connection_numerator[0][1]) &&
      append_blind(out.bytes, out.byte_count, "*dv) :\n");
}

HOLONICS_CALLABLE constexpr bool scalar_atom(const algebraic_variation_surface& surface,
    variation_formal_face& out, bool& first) noexcept {
  return atom_prefix(out, first) &&
      parameter_polynomial(out, surface.scalar_second, 3) &&
      append_blind(out.bytes, out.byte_count, "*ddu + ") &&
      parameter_polynomial(out, surface.scalar_first, 2) &&
      append_blind(out.bytes, out.byte_count, "*du + ") &&
      integer(out, surface.scalar_zeroth) &&
      append_blind(out.bytes, out.byte_count, "*u = 0") && atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool singular_hypotheses(
    const algebraic_variation_surface& surface, variation_formal_face& out) noexcept {
  return append_blind(out.bytes, out.byte_count, "    (hs0 : t ≠ ") &&
      integer(out, surface.collision_parameters[0]) &&
      append_blind(out.bytes, out.byte_count, ") (hs1 : t ≠ ") &&
      integer(out, surface.collision_parameters[1]) &&
      append_blind(out.bytes, out.byte_count, ")\n");
}

template<std::size_t Derivative>
HOLONICS_CALLABLE constexpr bool residual(variation_formal_face& out,
    const algebraic_variation_surface& surface, std::uint8_t row,
    const char (&derivative)[Derivative]) noexcept {
  return connection_denominator(surface, out) &&
      append_blind(out.bytes, out.byte_count, "*") &&
      append_blind(out.bytes, out.byte_count, derivative) &&
      append_blind(out.bytes, out.byte_count, "-") &&
      affine(out, surface.connection_numerator[row][0]) &&
      append_blind(out.bytes, out.byte_count, "*u-") &&
      affine(out, surface.connection_numerator[row][1]) &&
      append_blind(out.bytes, out.byte_count, "*v");
}

HOLONICS_CALLABLE constexpr bool elimination_inner(
    const algebraic_variation_surface& surface, variation_formal_face& out) noexcept {
  return append_blind(out.bytes, out.byte_count, "(-2)*") &&
      affine(out, surface.connection_numerator[0][1]) &&
      append_blind(out.bytes, out.byte_count, "*dv + ") &&
      integer(out, surface.scalar_zeroth) &&
      append_blind(out.bytes, out.byte_count, "*u + 2*") &&
      affine(out, surface.connection_numerator[1][1]) &&
      append_blind(out.bytes, out.byte_count, "*du");
}

HOLONICS_CALLABLE constexpr bool scalar_proof(
    const algebraic_variation_surface& surface, variation_formal_face& out) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "  constructor\n  · have hD : ") ||
      !connection_denominator(surface, out) ||
      !append_blind(out.bytes, out.byte_count, " ≠ 0 := by\n"
          "      have hs0' : t - ") || !integer(out, surface.collision_parameters[0]) ||
      !append_blind(out.bytes, out.byte_count, " ≠ 0 := sub_ne_zero.mpr hs0\n"
          "      have hs1' : ") || !integer(out, surface.collision_parameters[1]) ||
      !append_blind(out.bytes, out.byte_count, " - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)\n"
          "      have hfactor : ") || !connection_denominator(surface, out) ||
      !append_blind(out.bytes, out.byte_count, " = ") ||
      !integer(out, surface.connection_scale) ||
      !append_blind(out.bytes, out.byte_count, "*(t-") ||
      !integer(out, surface.collision_parameters[0]) ||
      !append_blind(out.bytes, out.byte_count, ")*(") ||
      !integer(out, surface.collision_parameters[1]) ||
      !append_blind(out.bytes, out.byte_count, "-t) := by ring\n"
          "      rw [hfactor]\n"
          "      exact mul_ne_zero (mul_ne_zero (by norm_num) hs0') hs1'\n"
          "    have hr0 : ") || !residual(out, surface, 0, "du") ||
      !append_blind(out.bytes, out.byte_count, " = 0 := by linarith [h0]\n"
          "    have hr1 : ") || !residual(out, surface, 1, "dv") ||
      !append_blind(out.bytes, out.byte_count, " = 0 := by linarith [h1]\n"
          "    have hm : ") || !connection_denominator(surface, out) ||
      !append_blind(out.bytes, out.byte_count, " * (") ||
      !elimination_inner(surface, out) ||
      !append_blind(out.bytes, out.byte_count, ") = 0 := by\n"
          "      calc\n        _ = (-2)*") ||
      !affine(out, surface.connection_numerator[0][1]) ||
      !append_blind(out.bytes, out.byte_count, "*(") ||
      !residual(out, surface, 1, "dv") ||
      !append_blind(out.bytes, out.byte_count, ") + (-2)*") ||
      !affine(out, surface.connection_numerator[0][0]) ||
      !append_blind(out.bytes, out.byte_count, "*(") ||
      !residual(out, surface, 0, "du") ||
      !append_blind(out.bytes, out.byte_count,
          ") := by ring\n        _ = 0 := by rw [hr0, hr1]; ring\n"
          "    have hv : ") || !elimination_inner(surface, out) ||
      !append_blind(out.bytes, out.byte_count,
          " = 0 := (mul_eq_zero.mp hm).resolve_left hD\n"
          "    nlinarith [hd, hv]\n")) { return false; }
  return true;
}

}  // namespace holonics::codec::variation_render_detail
