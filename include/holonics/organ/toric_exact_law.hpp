#pragma once

#include <holonics/organ/toric_cycle_schema.hpp>

namespace holonics::organ::toric_exact {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t absolute(
    std::int64_t value) noexcept { return value < 0 ? -value : value; }

struct unsigned_division final {
  std::uint64_t quotient{};
  std::uint64_t remainder{};
};

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

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational make(
    std::int64_t numerator, std::int64_t denominator = 1) noexcept {
  if (denominator == 0) { return {0, 0}; }
  if (denominator < 0) { numerator = -numerator; denominator = -denominator; }
  const auto divisor = gcd(numerator, denominator);
  return {quotient(numerator, divisor), quotient(denominator, divisor)};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t next(
    std::uint8_t index, std::uint8_t count) noexcept {
  return static_cast<std::uint8_t>(index + 1U == count ? 0U : index + 1U);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t previous(
    std::uint8_t index, std::uint8_t count) noexcept {
  return index == 0 ? static_cast<std::uint8_t>(count - 1U) :
      static_cast<std::uint8_t>(index - 1U);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid(toric_rational value) noexcept {
  return value.denominator > 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    toric_rational left, toric_rational right) noexcept {
  left = make(left.numerator, left.denominator);
  right = make(right.numerator, right.denominator);
  return valid(left) && valid(right) && left.numerator == right.numerator &&
      left.denominator == right.denominator;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational add(
    toric_rational left, toric_rational right) noexcept {
  return make(left.numerator * right.denominator +
      right.numerator * left.denominator, left.denominator * right.denominator);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational subtract(
    toric_rational left, toric_rational right) noexcept {
  return add(left, {-right.numerator, right.denominator});
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational multiply(
    toric_rational left, toric_rational right) noexcept {
  return make(left.numerator * right.numerator, left.denominator * right.denominator);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr toric_rational divide(
    toric_rational left, toric_rational right) noexcept {
  return make(left.numerator * right.denominator, left.denominator * right.numerator);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t determinant(
    toric_integer_pair left, toric_integer_pair right) noexcept {
  return left.x * right.y - left.y * right.x;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t dot(
    toric_integer_pair left, toric_integer_pair right) noexcept {
  return left.x * right.x + left.y * right.y;
}

}  // namespace holonics::organ::toric_exact
