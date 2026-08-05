#pragma once

#include <cstdint>

#include <holonics/exact/config.hpp>

namespace holonics::exact {

struct small_rational final {
  std::int64_t numerator{};
  std::int64_t denominator{1};
};

namespace small_rational_law {

struct unsigned_division final {
  std::uint64_t quotient{};
  std::uint64_t remainder{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t absolute(
    std::int64_t value) noexcept { return value < 0 ? -value : value; }

[[nodiscard]] HOLONICS_CALLABLE constexpr unsigned_division divide_unsigned(
    std::uint64_t dividend, std::uint64_t divisor) noexcept {
  unsigned_division result{};
  if (divisor == 0) { return result; }
  for (std::uint8_t step = 64; step != 0; --step) {
    const auto bit = static_cast<std::uint8_t>(step - 1U);
    result.remainder = (result.remainder << 1U) | ((dividend >> bit) & 1U);
    if (result.remainder >= divisor) {
      result.remainder -= divisor;
      result.quotient |= std::uint64_t{1} << bit;
    }
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t quotient(
    std::int64_t dividend, std::int64_t divisor) noexcept {
  if (divisor == 0) { return 0; }
  const bool negative = (dividend < 0) != (divisor < 0);
  const auto result = divide_unsigned(static_cast<std::uint64_t>(absolute(dividend)),
      static_cast<std::uint64_t>(absolute(divisor)));
  const auto magnitude = static_cast<std::int64_t>(result.quotient);
  return negative ? -magnitude : magnitude;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t remainder(
    std::int64_t dividend, std::int64_t divisor) noexcept {
  if (divisor == 0) { return 0; }
  return static_cast<std::int64_t>(divide_unsigned(
      static_cast<std::uint64_t>(absolute(dividend)),
      static_cast<std::uint64_t>(absolute(divisor))).remainder);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t gcd(
    std::int64_t left, std::int64_t right) noexcept {
  left = absolute(left); right = absolute(right);
  while (right != 0) {
    const auto residue = remainder(left, right); left = right; right = residue;
  }
  return left == 0 ? 1 : left;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr small_rational make(
    std::int64_t numerator, std::int64_t denominator = 1) noexcept {
  if (denominator == 0) { return {0, 0}; }
  if (denominator < 0) { numerator = -numerator; denominator = -denominator; }
  const auto divisor = gcd(numerator, denominator);
  return {quotient(numerator, divisor), quotient(denominator, divisor)};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid(small_rational value) noexcept {
  return value.denominator > 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    small_rational left, small_rational right) noexcept {
  left = make(left.numerator, left.denominator);
  right = make(right.numerator, right.denominator);
  return valid(left) && valid(right) && left.numerator == right.numerator &&
      left.denominator == right.denominator;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr small_rational add(
    small_rational left, small_rational right) noexcept {
  const auto shared = gcd(left.denominator, right.denominator);
  const auto left_scale = quotient(right.denominator, shared);
  const auto right_scale = quotient(left.denominator, shared);
  return make(left.numerator * left_scale + right.numerator * right_scale,
              right_scale * right.denominator);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr small_rational negate(
    small_rational value) noexcept { return {-value.numerator, value.denominator}; }

[[nodiscard]] HOLONICS_CALLABLE constexpr small_rational subtract(
    small_rational left, small_rational right) noexcept { return add(left, negate(right)); }

[[nodiscard]] HOLONICS_CALLABLE constexpr small_rational multiply(
    small_rational left, small_rational right) noexcept {
  const auto left_cancel = gcd(left.numerator, right.denominator);
  const auto right_cancel = gcd(right.numerator, left.denominator);
  return make(quotient(left.numerator, left_cancel) *
                  quotient(right.numerator, right_cancel),
              quotient(left.denominator, right_cancel) *
                  quotient(right.denominator, left_cancel));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr small_rational divide(
    small_rational left, small_rational right) noexcept {
  return right.numerator == 0
             ? small_rational{0, 0}
             : multiply(left, make(right.denominator, right.numerator));
}

}  // namespace small_rational_law
}  // namespace holonics::exact
