#pragma once

#include <holonics/organ/phase_crystal_cases.hpp>
#include <holonics/organ/phase_crystal_hull_law.hpp>
#include <holonics/organ/phase_crystal_series_law.hpp>
#include <holonics/organ/phase_crystal_shape_law.hpp>

namespace holonics::organ {
namespace phase_crystal_probe_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool boundary_receipt(
    const phase_case_definition& definition, phase_case_receipt& receipt) noexcept {
  std::int8_t first_residuals[phase_crystal_point_capacity]{};
  std::int8_t second_residuals[phase_crystal_point_capacity]{};
  const auto first_count = definition.first_modulus;
  const auto second_count = definition.second_modulus;
  for (std::uint16_t first = 0; first < first_count; ++first) {
    for (std::uint16_t second = 0; second < second_count; ++second) {
      const auto next_first = static_cast<std::uint16_t>(first + 1U == first_count ?
          0U : first + 1U);
      const auto next_second = static_cast<std::uint16_t>(second + 1U == second_count ?
          0U : second + 1U);
      const auto horizontal_bottom = static_cast<std::uint16_t>(first * second_count + second);
      const auto horizontal_top = static_cast<std::uint16_t>(first * second_count + next_second);
      const auto vertical_left = static_cast<std::uint16_t>(first * second_count + second);
      const auto vertical_right = static_cast<std::uint16_t>(next_first * second_count + second);
      ++first_residuals[horizontal_bottom];
      --first_residuals[horizontal_top];
      --second_residuals[vertical_left];
      ++second_residuals[vertical_right];
    }
  }
  std::int16_t residual = 0;
  const auto cells = static_cast<std::uint16_t>(first_count * second_count);
  for (std::uint16_t slot = 0; slot < cells; ++slot) {
    residual = static_cast<std::int16_t>(residual + first_residuals[slot]);
    residual = static_cast<std::int16_t>(residual + second_residuals[slot]);
    if (first_residuals[slot] != 0 || second_residuals[slot] != 0) { return false; }
  }
  receipt.boundary_residual = residual;
  receipt.complete_boundary_cancels = residual == 0;
  return receipt.complete_boundary_cancels;
}

}  // namespace phase_crystal_probe_detail

[[nodiscard]] HOLONICS_CALLABLE constexpr phase_case_receipt form_phase_crystal_case(
    const phase_crystal_foundation& foundation, std::uint16_t slot) noexcept {
  using namespace phase_crystal_detail;
  phase_case_receipt receipt{};
  receipt.identity = exact::word{foundation.case_seed.value() + slot};
  receipt.definition = phase_case(slot);
  const auto& definition = receipt.definition;
  if (!valid_phase_crystal_foundation(foundation) || slot >= foundation.case_count ||
      definition.first_modulus < 2 || definition.second_modulus < 2) { return receipt; }
  const std::uint64_t divisor = gcd(definition.first_modulus, definition.second_modulus);
  const std::uint64_t product =
      static_cast<std::uint64_t>(definition.first_modulus) * definition.second_modulus;
  std::uint64_t least = 0;
  std::uint64_t remainder = 0;
  if (!divide_unsigned(product, divisor, least, remainder) || remainder != 0) { return receipt; }
  receipt.gcd = static_cast<std::uint16_t>(divisor);
  receipt.lcm = static_cast<std::uint16_t>(least);
  receipt.orbit_count = receipt.gcd;
  receipt.orbit_length = receipt.lcm;
  receipt.vertex_count = static_cast<std::uint16_t>(product);
  receipt.phase_edge_count = static_cast<std::uint16_t>(2U * product);
  receipt.cell_count = static_cast<std::uint16_t>(product);
  receipt.seam_count = static_cast<std::uint16_t>(2U * product);
  receipt.coprime = divisor == 1;
  receipt.orbit_partition_exact = divisor * least == product;
  receipt.carrier_coordinate_dimension_four = true;
  receipt.cell_dimension_two = true;
  receipt.receiver_dimension_two = true;
  receipt.screen_crossings_are_contacts = false;
  const bool boundary = phase_crystal_probe_detail::boundary_receipt(definition, receipt);
  const bool shapes = shape_distribution(definition, receipt);
  const bool hull = hull_receipt(definition, receipt);
  const bool series = carry_gauss_112(receipt.orbit_length, receipt);
  receipt.exact = receipt.orbit_partition_exact && boundary && shapes && hull && series;
  return receipt;
}

}  // namespace holonics::organ
