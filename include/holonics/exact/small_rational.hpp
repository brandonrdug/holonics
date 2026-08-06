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

/// Restoring division, entered at the dividend's own leading bit.
///
/// A hardware `/` may not be used: on `sm_89` a sixty-four-bit divide lowers
/// through a Newton iteration whose opening instruction converts to a
/// non-integer carrier, and no such carrier may be reachable from a kernel. So
/// the division is carried in bits — but it is entered at the operand's width
/// rather than at sixty-four, because **the leading zeros of a small operand are
/// terrain the value already paid for.** Exact, and identical in return.
[[nodiscard]] HOLONICS_CALLABLE constexpr unsigned_division divide_unsigned(
    std::uint64_t dividend, std::uint64_t divisor) noexcept {
  unsigned_division result{};
  if (divisor == 0) { return result; }
  if (dividend < divisor) { result.remainder = dividend; return result; }
  std::uint8_t top = 63;
  while (((dividend >> top) & 1U) == 0) { --top; }
  for (std::int16_t step = top; step >= 0; --step) {
    const auto bit = static_cast<std::uint8_t>(step);
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

/// The common measure, taken by halving rather than by dividing.
///
/// Stein's construction: strip the shared twos, then repeatedly strip the odd
/// side's twos and subtract the smaller from the larger. **No division occurs at
/// all** — only shifts, comparison, and subtraction — so this path carries no
/// divide to be lowered and no carrier to be converted. It is called five times
/// per elimination step, which is why it is the one that had to stop dividing.
///
/// Returns exactly what the Euclidean form returned, including `1` for the
/// doubly-zero argument.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t gcd(
    std::int64_t left, std::int64_t right) noexcept {
  auto measured = static_cast<std::uint64_t>(absolute(left));
  auto against = static_cast<std::uint64_t>(absolute(right));
  if (measured == 0 || against == 0) {
    const auto standing = measured | against;
    return standing == 0 ? 1 : static_cast<std::int64_t>(standing);
  }
  std::uint8_t shared = 0;
  while (((measured | against) & 1U) == 0) {
    measured >>= 1U; against >>= 1U; ++shared;
  }
  while ((measured & 1U) == 0) { measured >>= 1U; }
  do {
    while ((against & 1U) == 0) { against >>= 1U; }
    if (measured > against) {
      const auto held = measured; measured = against; against = held;
    }
    against -= measured;
  } while (against != 0);
  return static_cast<std::int64_t>(measured << shared);
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
