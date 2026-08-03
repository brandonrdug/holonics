#pragma once

#include <cstdint>

#include <holonics/exact/config.hpp>

namespace holonics::exact {

enum class status : std::uint8_t {
  exact,
  capacity_refused,
  negative_refused,
  divide_by_zero,
  zero_denominator,
  invalid_modulus,
  noninvertible,
  invalid_projective_pair,
  degree_refused
};

struct operation_receipt final {
  status state{status::exact};
  std::uint16_t admitted_limbs{};
  std::uint16_t required_limbs{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return state == status::exact;
  }
};

template<class Value>
struct checked_result final {
  Value value{};
  operation_receipt receipt{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return receipt.accepted();
  }
};

}  // namespace holonics::exact
