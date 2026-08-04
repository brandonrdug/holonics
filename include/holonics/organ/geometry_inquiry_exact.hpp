#pragma once

#include <cstdint>

#include <holonics/exact/config.hpp>

namespace holonics::organ::geometry_inquiry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  if (~std::uint64_t{0} - left < right) { return false; }
  result = left + right;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  result = 0;
  while (right != 0) {
    if ((right & 1U) != 0 && !add(result, left, result)) { return false; }
    right >>= 1U;
    if (right != 0 && !add(left, left, left)) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool difference(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  if (left < right) { return false; }
  result = left - right;
  return true;
}

}  // namespace holonics::organ::geometry_inquiry_detail
