#pragma once

#include <cstdint>

#include <holonics/exact/config.hpp>
#include <holonics/organ/phase_crystal_schema.hpp>

namespace holonics::organ::phase_crystal_detail {

inline constexpr std::uint64_t signed_limit = 0x7fff'ffff'ffff'ffffULL;

HOLONICS_CALLABLE constexpr bool divide_unsigned(std::uint64_t dividend,
    std::uint64_t divisor, std::uint64_t& quotient, std::uint64_t& remainder) noexcept {
  if (divisor == 0) { return false; }
  quotient = 0;
  remainder = 0;
  for (std::uint16_t bit = 64; bit != 0; --bit) {
    remainder = (remainder << 1U) | ((dividend >> (bit - 1U)) & 1U);
    if (remainder >= divisor) {
      remainder -= divisor;
      quotient |= std::uint64_t{1} << (bit - 1U);
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t gcd(
    std::uint64_t left, std::uint64_t right) noexcept {
  while (right != 0) {
    std::uint64_t quotient = 0;
    std::uint64_t remainder = 0;
    if (!divide_unsigned(left, right, quotient, remainder)) { return 0; }
    left = right;
    right = remainder;
  }
  return left;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply_unsigned(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  result = 0;
  if (left > signed_limit) { return false; }
  while (right != 0) {
    if ((right & 1U) != 0) {
      if (result > signed_limit - left) { return false; }
      result += left;
    }
    right >>= 1U;
    if (right != 0) {
      if (left > signed_limit - left) { return false; }
      left += left;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t magnitude(
    std::int64_t value) noexcept {
  return value < 0 ? static_cast<std::uint64_t>(-(value + 1)) + 1U :
      static_cast<std::uint64_t>(value);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply_signed(
    std::int64_t left, std::int64_t right, std::int64_t& result) noexcept {
  std::uint64_t product = 0;
  if (!multiply_unsigned(magnitude(left), magnitude(right), product)) { return false; }
  result = (left < 0) != (right < 0) ? -static_cast<std::int64_t>(product) :
      static_cast<std::int64_t>(product);
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add_signed(
    std::int64_t left, std::int64_t right, std::int64_t& result) noexcept {
  if ((right > 0 && left > static_cast<std::int64_t>(signed_limit) - right) ||
      (right < 0 && left < -static_cast<std::int64_t>(signed_limit) - right)) { return false; }
  result = left + right;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr phase_ratio normalize(
    std::int64_t numerator, std::uint64_t denominator) noexcept {
  if (denominator == 0 || magnitude(numerator) > signed_limit) { return {0, 0}; }
  if (numerator == 0) { return {}; }
  const auto divisor = gcd(magnitude(numerator), denominator);
  std::uint64_t numerator_quotient = 0;
  std::uint64_t numerator_remainder = 0;
  std::uint64_t denominator_quotient = 0;
  std::uint64_t denominator_remainder = 0;
  if (!divide_unsigned(magnitude(numerator), divisor,
          numerator_quotient, numerator_remainder) ||
      !divide_unsigned(denominator, divisor,
          denominator_quotient, denominator_remainder) ||
      numerator_remainder != 0 || denominator_remainder != 0) { return {0, 0}; }
  return {numerator < 0 ? -static_cast<std::int64_t>(numerator_quotient) :
      static_cast<std::int64_t>(numerator_quotient), denominator_quotient};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add(
    phase_ratio left, phase_ratio right, phase_ratio& result) noexcept {
  if (left.denominator == 0 || right.denominator == 0) { return false; }
  const auto divisor = gcd(left.denominator, right.denominator);
  std::uint64_t left_scale = 0;
  std::uint64_t right_scale = 0;
  std::uint64_t remainder = 0;
  if (!divide_unsigned(right.denominator, divisor, left_scale, remainder) || remainder != 0 ||
      !divide_unsigned(left.denominator, divisor, right_scale, remainder) || remainder != 0) {
    return false;
  }
  std::int64_t first = 0;
  std::int64_t second = 0;
  std::int64_t numerator = 0;
  std::uint64_t denominator = 0;
  if (!multiply_signed(left.numerator, static_cast<std::int64_t>(left_scale), first) ||
      !multiply_signed(right.numerator, static_cast<std::int64_t>(right_scale), second) ||
      !add_signed(first, second, numerator) ||
      !multiply_unsigned(left.denominator, left_scale, denominator)) { return false; }
  result = normalize(numerator, denominator);
  return result.denominator != 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool subtract(
    phase_ratio left, phase_ratio right, phase_ratio& result) noexcept {
  if (right.numerator == -static_cast<std::int64_t>(signed_limit) - 1) { return false; }
  right.numerator = -right.numerator;
  return add(left, right, result);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(
    phase_ratio left, phase_ratio right, phase_ratio& result) noexcept {
  if (left.denominator == 0 || right.denominator == 0) { return false; }
  const auto first_divisor = gcd(magnitude(left.numerator), right.denominator);
  const auto second_divisor = gcd(magnitude(right.numerator), left.denominator);
  std::uint64_t quotient = 0;
  std::uint64_t remainder = 0;
  if (!divide_unsigned(magnitude(left.numerator), first_divisor, quotient, remainder) ||
      remainder != 0) { return false; }
  left.numerator = left.numerator < 0 ? -static_cast<std::int64_t>(quotient) :
      static_cast<std::int64_t>(quotient);
  if (!divide_unsigned(right.denominator, first_divisor,
          right.denominator, remainder) || remainder != 0 ||
      !divide_unsigned(magnitude(right.numerator), second_divisor, quotient, remainder) ||
      remainder != 0) { return false; }
  right.numerator = right.numerator < 0 ? -static_cast<std::int64_t>(quotient) :
      static_cast<std::int64_t>(quotient);
  if (!divide_unsigned(left.denominator, second_divisor,
          left.denominator, remainder) || remainder != 0) { return false; }
  std::int64_t numerator = 0;
  std::uint64_t denominator = 0;
  if (!multiply_signed(left.numerator, right.numerator, numerator) ||
      !multiply_unsigned(left.denominator, right.denominator, denominator)) { return false; }
  result = normalize(numerator, denominator);
  return result.denominator != 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool scale(
    phase_ratio value, std::int64_t numerator, std::uint64_t denominator,
    phase_ratio& result) noexcept {
  const auto factor = normalize(numerator, denominator);
  return factor.denominator != 0 && multiply(value, factor, result);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr int compare(
    phase_ratio left, phase_ratio right, bool& exact) noexcept {
  if (left.denominator == 0 || right.denominator == 0) {
    exact = false;
    return 0;
  }
  const auto divisor = gcd(left.denominator, right.denominator);
  std::uint64_t left_scale = 0;
  std::uint64_t right_scale = 0;
  std::uint64_t remainder = 0;
  if (!divide_unsigned(right.denominator, divisor, left_scale, remainder) || remainder != 0 ||
      !divide_unsigned(left.denominator, divisor, right_scale, remainder) || remainder != 0) {
    exact = false;
    return 0;
  }
  std::int64_t first = 0;
  std::int64_t second = 0;
  if (!multiply_signed(left.numerator, static_cast<std::int64_t>(left_scale), first) ||
      !multiply_signed(right.numerator, static_cast<std::int64_t>(right_scale), second)) {
    exact = false;
    return 0;
  }
  return first < second ? -1 : (first > second ? 1 : 0);
}

}  // namespace holonics::organ::phase_crystal_detail
