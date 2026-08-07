#pragma once

#include <holonics/organ/phase_crystal_receipt.hpp>

namespace holonics::organ {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_phase_crystal_foundation(
    const phase_crystal_foundation& value) noexcept {
  return value.ecology.value() != 0 && value.product_cells.value() != 0 &&
      value.diagonal_transport.value() != 0 && value.receiver_projection.value() != 0 &&
      value.series_current.value() != 0 && value.provenance.value() != 0 &&
      value.case_seed.value() != 0 && value.case_count == phase_crystal_case_capacity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr phase_case_definition phase_case(
    std::uint16_t slot) noexcept {
  constexpr phase_case_definition cases[phase_crystal_case_capacity]{
      {2, 3, 1, 1, phase_case_kind::prime_pair, false, false},
      {3, 5, 1, 1, phase_case_kind::prime_pair, false, false},
      {5, 7, 1, 1, phase_case_kind::prime_pair, false, false},
      {7, 11, 1, 1, phase_case_kind::prime_pair, false, false},
      {11, 13, 1, 1, phase_case_kind::prime_pair, false, false},
      {13, 17, 1, 1, phase_case_kind::prime_pair, false, false},
      {17, 19, 1, 1, phase_case_kind::prime_pair, false, false},
      {4, 5, 1, 1, phase_case_kind::composite_coprime, false, false},
      {8, 9, 1, 1, phase_case_kind::composite_coprime, false, false},
      {6, 9, 1, 1, phase_case_kind::composite_shared_factor, false, false},
      {8, 12, 1, 1, phase_case_kind::composite_shared_factor, false, false},
      {7, 11, 1, 1, phase_case_kind::reversed_dominance, true, false},
      {7, 11, 25, 16, phase_case_kind::exact_dilation, false, false},
      {7, 11, 1, 1, phase_case_kind::exact_turn, false, true},
      {11, 7, 1, 1, phase_case_kind::reversed_pair, false, false},
      {9, 10, 1, 1, phase_case_kind::composite_coprime, false, false}};
  return slot < phase_crystal_case_capacity ? cases[slot] : phase_case_definition{};
}

}  // namespace holonics::organ
