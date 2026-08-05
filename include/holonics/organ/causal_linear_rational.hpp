#pragma once

#include <holonics/organ/blind_integer_exact.hpp>

namespace holonics::organ::causal_linear_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool checked_negate(
    std::int64_t value, std::int64_t& out) noexcept {
  if (value < -blind_integer_detail::exact_limit) { return false; }
  out = -value; return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_valid(
    exact::small_rational value) noexcept {
  return value.numerator >= -blind_integer_detail::exact_limit &&
      value.denominator > 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_make(std::int64_t numerator,
    std::int64_t denominator, exact::small_rational& out) noexcept {
  if (denominator == 0 || numerator < -blind_integer_detail::exact_limit ||
      denominator < -blind_integer_detail::exact_limit) { return false; }
  if (denominator < 0 && (!checked_negate(numerator, numerator) ||
      !checked_negate(denominator, denominator))) { return false; }
  const auto divisor = exact::small_rational_law::gcd(numerator, denominator);
  return blind_integer_detail::divide_exact(numerator, divisor, out.numerator) &&
      blind_integer_detail::divide_exact(denominator, divisor, out.denominator) &&
      rational_valid(out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_make(
    std::int64_t numerator, exact::small_rational& out) noexcept {
  return rational_make(numerator, 1, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_add(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  if (!rational_valid(left) || !rational_valid(right)) { return false; }
  std::int64_t first = 0; std::int64_t second = 0;
  std::int64_t numerator = 0; std::int64_t denominator = 0;
  return blind_integer_detail::multiply(left.numerator, right.denominator, first) &&
      blind_integer_detail::multiply(right.numerator, left.denominator, second) &&
      blind_integer_detail::add(first, second, numerator) &&
      blind_integer_detail::multiply(left.denominator, right.denominator, denominator) &&
      rational_make(numerator, denominator, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_negate(
    exact::small_rational value, exact::small_rational& out) noexcept {
  std::int64_t numerator = 0;
  return rational_valid(value) && checked_negate(value.numerator, numerator) &&
      rational_make(numerator, value.denominator, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_subtract(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  exact::small_rational negative{};
  return rational_negate(right, negative) && rational_add(left, negative, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_multiply(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  if (!rational_valid(left) || !rational_valid(right)) { return false; }
  std::int64_t numerator = 0; std::int64_t denominator = 0;
  return blind_integer_detail::multiply(left.numerator, right.numerator, numerator) &&
      blind_integer_detail::multiply(left.denominator, right.denominator, denominator) &&
      rational_make(numerator, denominator, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool rational_divide(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  if (!rational_valid(left) || !rational_valid(right) || right.numerator == 0) {
    return false;
  }
  std::int64_t numerator = 0; std::int64_t denominator = 0;
  return blind_integer_detail::multiply(left.numerator, right.denominator, numerator) &&
      blind_integer_detail::multiply(left.denominator, right.numerator, denominator) &&
      rational_make(numerator, denominator, out);
}

}  // namespace holonics::organ::causal_linear_detail
