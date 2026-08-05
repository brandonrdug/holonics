#pragma once

#include <holonics/codec/expression_geometry_renderer_equations.hpp>

namespace holonics::codec::expression_geometry_render_detail {

namespace equation = expression_geometry_equation_detail;

template<class Face>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool integer(Face& out, std::int64_t value) noexcept {
  return causal_linear_render_detail::integer(out, value);
}

template<class Face>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational(Face& out,
    exact::small_rational value) noexcept {
  return append_blind(out.bytes, out.byte_count, "((") && integer(out, value.numerator) &&
      append_blind(out.bytes, out.byte_count, " : ℚ) / ") &&
      integer(out, value.denominator) && append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool translated_polynomial(
    expression_geometry_formal_face& out, const expression_geometry_surface& source) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "(v^2")) { return false; }
  for (std::uint8_t offset = 0; offset < 6; ++offset) {
    const auto degree = static_cast<std::uint8_t>(5U - offset);
    if (!append_blind(out.bytes, out.byte_count, " + (") ||
        !integer(out, source.translated_constant[degree]) ||
        !append_blind(out.bytes, out.byte_count, " + ") ||
        !integer(out, source.translated_parameter[degree]) ||
        !append_blind(out.bytes, out.byte_count, "*t)*u^") || !integer(out, degree)) {
      return false;
    }
  }
  return append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool indicial(
    expression_geometry_formal_face& out, const std::int64_t (&coefficients)[5],
    bool infinity) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "(∀ r : ℤ, ((")) { return false; }
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (slot != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!integer(out, coefficients[slot]) || !append_blind(out.bytes, out.byte_count, "*r^") ||
        !integer(out, slot)) { return false; }
  }
  if (!append_blind(out.bytes, out.byte_count, ") = ")) { return false; }
  if (infinity) {
    return append_blind(out.bytes, out.byte_count,
        "(8*r+3)*(8*r+13)*(8*r+23)*(8*r+33)))");
  }
  return append_blind(out.bytes, out.byte_count, "r^2*(r-1)*(r-2)))");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool bezout(
    expression_geometry_formal_face& out, const expression_geometry_surface& source) noexcept {
  return append_blind(out.bytes, out.byte_count, "(∀ t x : ℤ, ") &&
      equation::x_polynomial(out, source.bezout_f) &&
      append_blind(out.bytes, out.byte_count, "*(x^5-t*x+") &&
      integer(out, source.family_constant) && append_blind(out.bytes, out.byte_count, ") + ") &&
      equation::x_polynomial(out, source.bezout_fx) &&
      append_blind(out.bytes, out.byte_count, "*(5*x^4-t) = ") &&
      equation::discriminant(out, source.resultant) && append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool reduction(
    expression_geometry_formal_face& out, const expression_geometry_surface& source,
    std::uint8_t basis) noexcept {
  return append_blind(out.bytes, out.byte_count, "(∀ t x : ℤ, ") &&
      equation::x_polynomial(out, source.reduction_p[basis]) &&
      append_blind(out.bytes, out.byte_count, "*(x^5-t*x+") &&
      integer(out, source.family_constant) && append_blind(out.bytes, out.byte_count, ") + ") &&
      equation::x_polynomial(out, source.reduction_q[basis]) &&
      append_blind(out.bytes, out.byte_count, "*(5*x^4-t) = ") &&
      equation::discriminant(out, source.resultant) && append_blind(out.bytes, out.byte_count, "*x^") &&
      integer(out, static_cast<std::int64_t>(basis + 1U)) &&
      append_blind(out.bytes, out.byte_count, ")");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool scalar(
    expression_geometry_formal_face& out, const expression_geometry_surface& source) noexcept {
  if (!append_blind(out.bytes, out.byte_count,
      "(∀ t z0 z1 z2 z3 z4 : ℤ, ((") || !integer(out, source.scalar[0]) ||
      !append_blind(out.bytes, out.byte_count, " + ") || !integer(out, source.scalar[1]) ||
      !append_blind(out.bytes, out.byte_count, "*t^5)*z4 + ") || !integer(out, source.scalar[2]) ||
      !append_blind(out.bytes, out.byte_count, "*t^4*z3 + ") || !integer(out, source.scalar[3]) ||
      !append_blind(out.bytes, out.byte_count, "*t^3*z2 + ") || !integer(out, source.scalar[4]) ||
      !append_blind(out.bytes, out.byte_count, "*t^2*z1 + ") || !integer(out, source.scalar[5]) ||
      !append_blind(out.bytes, out.byte_count, "*t*z0) = 16*")) { return false; }
  return equation::discriminant(out, source.resultant) && append_blind(out.bytes, out.byte_count,
      "*z4 - 61440*t^4*z3 - 247680*t^3*z2 - 264000*t^2*z1 - 29601*t*z0)");
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool recurrence(
    expression_geometry_formal_face& out, const expression_geometry_surface& source,
    std::uint8_t front) noexcept {
  constexpr std::int64_t leading[4]{120,360,840,1680};
  constexpr std::int64_t third[4]{0,0,0,6};
  constexpr std::int64_t second[4]{0,0,2,6};
  const auto first = static_cast<std::int64_t>(front);
  if (!append_blind(out.bytes, out.byte_count, "((") || !integer(out, source.scalar[0]) ||
      !append_blind(out.bytes, out.byte_count, " : ℚ)*") || !integer(out, leading[front]) ||
      !append_blind(out.bytes, out.byte_count, "*") ||
      !rational(out, source.series[front][front + 5U]) ||
      !append_blind(out.bytes, out.byte_count, " + (") || !integer(out, source.scalar[2]) ||
      !append_blind(out.bytes, out.byte_count, " : ℚ)*") || !integer(out, third[front]) ||
      !append_blind(out.bytes, out.byte_count, " + (") || !integer(out, source.scalar[3]) ||
      !append_blind(out.bytes, out.byte_count, " : ℚ)*") || !integer(out, second[front]) ||
      !append_blind(out.bytes, out.byte_count, " + (") || !integer(out, source.scalar[4]) ||
      !append_blind(out.bytes, out.byte_count, " : ℚ)*") || !integer(out, first) ||
      !append_blind(out.bytes, out.byte_count, " + (") || !integer(out, source.scalar[5]) ||
      !append_blind(out.bytes, out.byte_count, " : ℚ) = 0)")) { return false; }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool residue(
    expression_geometry_formal_face& out, const expression_geometry_surface& source) noexcept {
  if (!append_blind(out.bytes, out.byte_count, "(∀ a : ℚ, 4*a^5=1 → ") ||
      !equation::algebraic_value(out, source.residue[0][0]) ||
      !append_blind(out.bytes, out.byte_count, " ≠ 0 ∧ (") ) { return false; }
  for (std::uint8_t column = 0; column < 4; ++column) {
    if (column != 0 && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!equation::algebraic_value(out, source.residue[0][column]) ||
        !append_blind(out.bytes, out.byte_count, "*a^") || !integer(out, column)) { return false; }
  }
  return append_blind(out.bytes, out.byte_count, ") = 0)");
}

}  // namespace holonics::codec::expression_geometry_render_detail

#include <holonics/codec/expression_geometry_renderer_bundle.hpp>

namespace holonics::codec {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool render_expression_geometry(
    const expression_geometry_surface& source, expression_geometry_formal_face& out) noexcept {
  return expression_geometry_render_detail::render_bundle(source, out);
}

}  // namespace holonics::codec
