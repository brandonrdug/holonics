#pragma once

#include <cstdint>

namespace holonics::tests {
struct r30_reference_result final {
  std::int32_t area[4]{};
  std::int32_t boundary[4]{};
  std::int32_t interior[4]{};
  std::int32_t counts[4][5]{};
  bool exact{};
};
[[nodiscard]] r30_reference_result r30_reference() noexcept;
[[nodiscard]] std::int64_t r30_reference_jacobian(std::uint8_t alpha,
                                                  std::uint8_t beta,
                                                  std::uint8_t row,
                                                  std::uint8_t column) noexcept;
} // namespace holonics::tests
