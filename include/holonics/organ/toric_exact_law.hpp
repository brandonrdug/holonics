#pragma once

#include <holonics/organ/toric_cycle_schema.hpp>

namespace holonics::organ::toric_exact {

using exact::small_rational_law::absolute;
using exact::small_rational_law::add;
using exact::small_rational_law::divide;
using exact::small_rational_law::equal;
using exact::small_rational_law::gcd;
using exact::small_rational_law::make;
using exact::small_rational_law::multiply;
using exact::small_rational_law::quotient;
using exact::small_rational_law::remainder;
using exact::small_rational_law::subtract;
using exact::small_rational_law::valid;

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t next(
    std::uint8_t index, std::uint8_t count) noexcept {
  return static_cast<std::uint8_t>(index + 1U == count ? 0U : index + 1U);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t previous(
    std::uint8_t index, std::uint8_t count) noexcept {
  return index == 0 ? static_cast<std::uint8_t>(count - 1U) :
      static_cast<std::uint8_t>(index - 1U);
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
