#pragma once

#include <holonics/codec/causal_linear_renderer_helpers.hpp>
#include <holonics/codec/expression_geometry_face.hpp>

namespace holonics::codec::expression_geometry_equation_detail {

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool nonzero(
    const std::int64_t (&value)[Capacity]) noexcept {
  for (const auto coefficient : value) {
    if (coefficient != 0) { return true; }
  }
  return false;
}

template<class Face, std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool parameter_polynomial(
    Face& out, const std::int64_t (&value)[Capacity]) noexcept {
  bool first = true;
  if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
  for (std::size_t degree = 0; degree < Capacity; ++degree) {
    if (value[degree] == 0) { continue; }
    if (!first && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!causal_linear_render_detail::integer(out, value[degree]) ||
        !append_blind(out.bytes, out.byte_count, "*") ||
        !append_blind(out.bytes, out.byte_count, "t") ||
        !append_blind(out.bytes, out.byte_count, "^" ) ||
        !causal_linear_render_detail::integer(out, static_cast<std::int64_t>(degree))) {
      return false;
    }
    first = false;
  }
  if (first && !append_blind(out.bytes, out.byte_count, "0")) { return false; }
  return append_blind(out.bytes, out.byte_count, ")");
}

template<class Face, std::size_t X, std::size_t T>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool x_polynomial(
    Face& out, const std::int64_t (&value)[X][T]) noexcept {
  bool first = true;
  if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
  for (std::size_t degree = 0; degree < X; ++degree) {
    if (!nonzero(value[degree])) { continue; }
    if (!first && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!parameter_polynomial(out, value[degree]) ||
        !append_blind(out.bytes, out.byte_count, "*x^") ||
        !causal_linear_render_detail::integer(out, static_cast<std::int64_t>(degree))) {
      return false;
    }
    first = false;
  }
  if (first && !append_blind(out.bytes, out.byte_count, "0")) { return false; }
  return append_blind(out.bytes, out.byte_count, ")");
}

template<class Face>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool discriminant(
    Face& out, const std::int64_t (&value)[6]) noexcept {
  return parameter_polynomial(out, value);
}

template<class Face>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool algebraic_value(
    Face& out, const exact::small_rational (&value)[5]) noexcept {
  bool first = true;
  if (!append_blind(out.bytes, out.byte_count, "(")) { return false; }
  for (std::uint8_t degree = 0; degree < 5; ++degree) {
    if (value[degree].numerator == 0) { continue; }
    if (!first && !append_blind(out.bytes, out.byte_count, " + ")) { return false; }
    if (!append_blind(out.bytes, out.byte_count, "((") ||
        !causal_linear_render_detail::integer(out, value[degree].numerator) ||
        !append_blind(out.bytes, out.byte_count, " : ℚ) / ") ||
        !causal_linear_render_detail::integer(out, value[degree].denominator) ||
        !append_blind(out.bytes, out.byte_count, ")*a^") ||
        !causal_linear_render_detail::integer(out, degree)) { return false; }
    first = false;
  }
  if (first && !append_blind(out.bytes, out.byte_count, "0")) { return false; }
  return append_blind(out.bytes, out.byte_count, ")");
}

}  // namespace holonics::codec::expression_geometry_equation_detail
