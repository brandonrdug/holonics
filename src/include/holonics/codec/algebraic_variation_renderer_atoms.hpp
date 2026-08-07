#pragma once

#include <holonics/codec/algebraic_variation_face.hpp>

namespace holonics::codec::variation_render_detail {

HOLONICS_CALLABLE constexpr bool integer(variation_formal_face& out,
    std::int64_t value) noexcept {
  return append_blind_integer(out.bytes, out.byte_count, value);
}

HOLONICS_CALLABLE constexpr bool atom_prefix(variation_formal_face& out,
    bool& first) noexcept {
  const bool returned = first ? append_blind(out.bytes, out.byte_count, "  (") :
      append_blind(out.bytes, out.byte_count, " ∧\n  (");
  first = false; return returned;
}

HOLONICS_CALLABLE constexpr bool atom_suffix(variation_formal_face& out) noexcept {
  return append_blind(out.bytes, out.byte_count, ")");
}

HOLONICS_CALLABLE constexpr bool affine(variation_formal_face& out,
    const std::int64_t value[2]) noexcept {
  return append_blind(out.bytes, out.byte_count, "(") && integer(out, value[0]) &&
      append_blind(out.bytes, out.byte_count, " + ") && integer(out, value[1]) &&
      append_blind(out.bytes, out.byte_count, "*t)");
}

HOLONICS_CALLABLE constexpr bool parameter_polynomial(variation_formal_face& out,
    const std::int64_t* coefficients, std::uint8_t count) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
  for (std::uint8_t slot = 0; slot < count; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, coefficients[slot]) ||
        !append_blind(out.bytes, out.byte_count, "*t^") || !integer(out, slot)) {
      return false;
    }
  }
  return append_blind(out.bytes, out.byte_count, ")");
}

HOLONICS_CALLABLE constexpr bool family_polynomial(const algebraic_variation_surface& surface,
    variation_formal_face& out, bool parameter_derivative, bool x_derivative) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
  const std::uint8_t first = x_derivative ? 1 : 0;
  for (std::uint8_t power = first; power < 4; ++power) {
    if (power != first && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    const std::int64_t coefficient[2]{
        parameter_derivative ? surface.polynomial[power][1] :
            surface.polynomial[power][0],
        parameter_derivative ? 0 : surface.polynomial[power][1]};
    if (!integer(out, x_derivative ? power : 1) ||
        !append_blind(out.bytes, out.byte_count, "*") || !affine(out, coefficient) ||
        !append_blind(out.bytes, out.byte_count, "*x^") ||
        !integer(out, x_derivative ? power - 1U : power)) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, ")");
}

HOLONICS_CALLABLE constexpr bool witness_polynomial(const algebraic_variation_surface& surface,
    variation_formal_face& out, std::uint8_t form, bool derivative) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
  const std::uint8_t first = derivative ? 1 : 0;
  for (std::uint8_t power = first; power < 3; ++power) {
    if (power != first && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, derivative ? power : 1) ||
        !append_blind(out.bytes, out.byte_count, "*") ||
        !affine(out, surface.witness[form][power]) ||
        !append_blind(out.bytes, out.byte_count, "*x^") ||
        !integer(out, derivative ? power - 1U : power)) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, ")");
}

HOLONICS_CALLABLE constexpr bool polynomial_atom(const algebraic_variation_surface& surface,
    variation_formal_face& out, bool& first) noexcept {
  if (!atom_prefix(out, first) ||
      !append_blind(out.bytes, out.byte_count, "(") ||
      !affine(out, surface.polynomial[2]) || !append_blind(out.bytes, out.byte_count, "^2*") ||
      !affine(out, surface.polynomial[1]) || !append_blind(out.bytes, out.byte_count, "^2 - 4*") ||
      !affine(out, surface.polynomial[3]) || !append_blind(out.bytes, out.byte_count, "*") ||
      !affine(out, surface.polynomial[1]) || !append_blind(out.bytes, out.byte_count, "^3 - 4*") ||
      !affine(out, surface.polynomial[2]) || !append_blind(out.bytes, out.byte_count, "^3*") ||
      !affine(out, surface.polynomial[0]) || !append_blind(out.bytes, out.byte_count, " - 27*") ||
      !affine(out, surface.polynomial[3]) || !append_blind(out.bytes, out.byte_count, "^2*") ||
      !affine(out, surface.polynomial[0]) || !append_blind(out.bytes, out.byte_count, "^2 + 18*") ||
      !affine(out, surface.polynomial[3]) || !append_blind(out.bytes, out.byte_count, "*") ||
      !affine(out, surface.polynomial[2]) || !append_blind(out.bytes, out.byte_count, "*") ||
      !affine(out, surface.polynomial[1]) || !append_blind(out.bytes, out.byte_count, "*") ||
      !affine(out, surface.polynomial[0]) || !append_blind(out.bytes, out.byte_count, ") = ") ||
      !parameter_polynomial(out, surface.discriminant, 5)) { return false; }
  return atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool reduction_atom(const algebraic_variation_surface& surface,
    variation_formal_face& out, bool& first, std::uint8_t form) noexcept {
  if (!atom_prefix(out, first) || !append_blind(out.bytes, out.byte_count, "(-") ||
      !integer(out, surface.connection_scale) || !append_blind(out.bytes, out.byte_count, "*") ||
      !parameter_polynomial(out, surface.connection_pole, 3) ||
      !append_blind(out.bytes, out.byte_count, ")*x^") || !integer(out, form) ||
      !append_blind(out.bytes, out.byte_count, "*") ||
      !family_polynomial(surface, out, true, false) ||
      !append_blind(out.bytes, out.byte_count, " - 2*(") ||
      !affine(out, surface.connection_numerator[form][0]) ||
      !append_blind(out.bytes, out.byte_count, " + ") ||
      !affine(out, surface.connection_numerator[form][1]) ||
      !append_blind(out.bytes, out.byte_count, "*x)*") ||
      !family_polynomial(surface, out, false, false) ||
      !append_blind(out.bytes, out.byte_count, " - 2*") ||
      !integer(out, surface.connection_scale) || !append_blind(out.bytes, out.byte_count, "*") ||
      !witness_polynomial(surface, out, form, true) ||
      !append_blind(out.bytes, out.byte_count, "*") ||
      !family_polynomial(surface, out, false, false) ||
      !append_blind(out.bytes, out.byte_count, " + ") ||
      !integer(out, surface.connection_scale) || !append_blind(out.bytes, out.byte_count, "*") ||
      !witness_polynomial(surface, out, form, false) ||
      !append_blind(out.bytes, out.byte_count, "*") ||
      !family_polynomial(surface, out, false, true) ||
      !append_blind(out.bytes, out.byte_count, " = 0")) { return false; }
  return atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool matrix_atom(variation_formal_face& out, bool& first,
    const std::int64_t left[2][2], const std::int64_t right[2][2],
    bool product) noexcept {
  if (!atom_prefix(out, first)) { return false; }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      if (row != 0 || column != 0) {
        if (!append_blind(out.bytes, out.byte_count, " ∧ ")) { return false; }
      }
      if (!append_blind(out.bytes, out.byte_count, "(") ||
          !integer(out, left[row][0]) ||
          !append_blind(out.bytes, out.byte_count, " * ") ||
          !integer(out, right[0][column]) ||
          !append_blind(out.bytes, out.byte_count, " + ") ||
          !integer(out, left[row][1]) ||
          !append_blind(out.bytes, out.byte_count, " * ") ||
          !integer(out, right[1][column]) ||
          !append_blind(out.bytes, out.byte_count, " : ℤ) = ") ||
          !integer(out, product && row == column ? 1 : 0)) { return false; }
    }
  }
  return atom_suffix(out);
}

HOLONICS_CALLABLE constexpr bool recurrence_atom(const algebraic_variation_surface& surface,
    variation_formal_face& out, bool& first, std::uint8_t n) noexcept {
  const auto& left = surface.series[n + 1U]; const auto& right = surface.series[n];
  return atom_prefix(out, first) && append_blind(out.bytes, out.byte_count, "(") &&
      integer(out, 4 * (n + 1U) * (n + 1U)) && append_blind(out.bytes, out.byte_count,
      " : ℚ) * (") && integer(out, left.numerator) &&
      append_blind(out.bytes, out.byte_count, " / ") && integer(out, left.denominator) &&
      append_blind(out.bytes, out.byte_count, ") = ") && integer(out, (2 * n + 1U) *
      (2 * n + 1U)) && append_blind(out.bytes, out.byte_count, " * (") &&
      integer(out, right.numerator) && append_blind(out.bytes, out.byte_count, " / ") &&
      integer(out, right.denominator) && append_blind(out.bytes, out.byte_count, ")") &&
      atom_suffix(out);
}

}  // namespace holonics::codec::variation_render_detail
