#pragma once

#include <cstdint>

#include <holonics/receiver/geometry_receipt.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool geometry_add(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  if (left > ~std::uint64_t{0} - right) { return false; }
  result = left + right;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool geometry_multiply(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  result = 0;
  while (right != 0) {
    if ((right & 1U) != 0 && !geometry_add(result, left, result)) { return false; }
    right >>= 1U;
    if (right != 0 && !geometry_add(left, left, left)) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr signed_word geometry_signed_difference(
    std::uint64_t positive, std::uint64_t negative) noexcept {
  if (positive >= negative) { return {exact::word{positive - negative}, false}; }
  return {exact::word{negative - positive}, true};
}

}  // namespace holonics::receiver
