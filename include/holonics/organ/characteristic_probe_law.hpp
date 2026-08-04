#pragma once

#include <holonics/organ/characteristic_shape_law.hpp>
#include <holonics/organ/phase_crystal_cases.hpp>

namespace holonics::organ {

[[nodiscard]] HOLONICS_CALLABLE constexpr characteristic_case_receipt
form_characteristic_case(const characteristic_foundation& foundation,
    std::uint16_t slot) noexcept {
  characteristic_case_receipt receipt{};
  receipt.identity = exact::word{foundation.case_seed.value() + slot};
  receipt.definition = phase_case(slot);
  if (!characteristic_detail::valid_foundation(foundation) ||
      slot >= foundation.case_count) { return receipt; }
  const auto product = static_cast<std::uint64_t>(receipt.definition.first_modulus) *
      receipt.definition.second_modulus;
  const auto divisor = phase_crystal_detail::gcd(receipt.definition.first_modulus,
      receipt.definition.second_modulus);
  std::uint64_t least = 0;
  std::uint64_t remainder = 0;
  if (divisor == 0 || !phase_crystal_detail::divide_unsigned(
          product, divisor, least, remainder) || remainder != 0 ||
      divisor > characteristic_tour_capacity) { return receipt; }
  receipt.gcd = static_cast<std::uint16_t>(divisor);
  receipt.lcm = static_cast<std::uint16_t>(least);
  receipt.vertices = static_cast<std::uint16_t>(product);
  receipt.tours = receipt.gcd;
  receipt.tour_length = receipt.lcm;
  receipt.characteristic_degree = receipt.vertices;
  receipt.minimal_degree = receipt.lcm;
  receipt.mode_multiplicity = receipt.gcd;
  receipt.orbit_exact = divisor * least == product;
  receipt.characteristic_factor_exact = receipt.orbit_exact;
  receipt.minimal_factor_exact = receipt.orbit_exact;
  receipt.cycle_factor_squarefree = receipt.lcm != 0;
  receipt.global_discriminant_zero = receipt.gcd > 1;
  receipt.local_transport_singular = false;
  const bool shapes = characteristic_detail::carry_shape_transport(receipt);
  receipt.exact = receipt.orbit_exact && receipt.characteristic_factor_exact &&
      receipt.minimal_factor_exact && receipt.cycle_factor_squarefree && shapes;
  return receipt;
}

}  // namespace holonics::organ
