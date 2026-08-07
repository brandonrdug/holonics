#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_field_law.hpp>
#include <holonics/organ/arithmetic_spectral_receipt.hpp>

namespace holonics::organ::arithmetic_aperture_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::uint32_t curve_fixed_width(
    const arithmetic_curve_receipt& curve) noexcept {
  std::uint32_t width = 0;
  for (std::uint8_t degree = 1; degree <= arithmetic_degree_count; ++degree) {
    width += arithmetic_field_detail::power_u32(curve.source.prime, degree);
  }
  return width;
}

[[nodiscard]] HOLONICS_CALLABLE inline bool fixed_coordinate(
    const arithmetic_spectral_receipt& inquiry, std::uint32_t global,
    std::uint8_t& curve, std::uint8_t& degree, std::uint32_t& x) noexcept {
  for (curve = 0; curve < arithmetic_curve_count; ++curve) {
    const auto width = curve_fixed_width(inquiry.curves[curve]);
    if (global >= width) { global -= width; continue; }
    for (degree = 1; degree <= arithmetic_degree_count; ++degree) {
      const auto q = arithmetic_field_detail::power_u32(inquiry.curves[curve].source.prime, degree);
      if (global < q) { x = global; return true; }
      global -= q;
    }
  }
  return false;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::uint32_t curve_pair_width(
    const arithmetic_curve_receipt& curve) noexcept {
  return 1U + arithmetic_field_detail::power_u32(curve.source.prime, 4);
}

[[nodiscard]] HOLONICS_CALLABLE inline bool pair_coordinate(
    const arithmetic_spectral_receipt& inquiry, std::uint32_t global,
    std::uint8_t& curve, std::uint32_t& pair) noexcept {
  for (curve = 0; curve < arithmetic_curve_count; ++curve) {
    const auto width = curve_pair_width(inquiry.curves[curve]);
    if (global < width) { pair = global; return true; }
    global -= width;
  }
  return false;
}

}  // namespace holonics::organ::arithmetic_aperture_detail
