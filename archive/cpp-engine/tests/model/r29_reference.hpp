#pragma once

#include <cstdint>

#include "r29_reference_field.hpp"

namespace holonics::tests {

struct r29_reference_curve final {
  std::uint16_t prime{}; std::uint16_t coefficient{};
  std::uint32_t counts[4]{}; std::int8_t real{}; std::int8_t imaginary{};
  std::uint32_t quadratic_points{}; bool exact{};
};

struct r29_reference_result final {
  r29_reference_detail::field fields[2][4]{};
  r29_reference_curve curves[7]{};
  bool exact{};
};

[[nodiscard]] r29_reference_result r29_reference() noexcept;

}  // namespace holonics::tests
