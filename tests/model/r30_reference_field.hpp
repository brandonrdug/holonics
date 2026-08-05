#pragma once

#include <cstdint>

namespace holonics::tests {

struct r30_reference_injection final {
  std::uint8_t side{};
  std::uint8_t subset{};
  std::uint8_t forbidden{};
  std::uint8_t image[3]{};
  std::uint8_t size{};
  std::int64_t weight{};
};
struct r30_reference_factor final {
  std::uint8_t p_size{};
  std::uint8_t q_size{};
  std::int16_t p_leading{};
  std::int16_t q_leading{};
  std::int64_t row_factor{};
};
struct r30_reference_point final {
  bool in_box{};
  bool included{};
  bool boundary{};
};
struct r30_reference_subset final {
  std::uint8_t columns[4]{};
  std::uint8_t witness{};
  bool saturated{};
};
struct r30_reference_pair final {
  std::uint8_t x{};
  std::uint8_t y{};
  std::uint8_t witness{};
  bool left{};
  bool right{};
};

[[nodiscard]] bool
r30_reference_injection_at(std::uint8_t, std::uint16_t,
                           r30_reference_injection &) noexcept;
[[nodiscard]] std::int64_t r30_reference_evaluation(std::uint8_t, std::uint8_t,
                                                    std::uint8_t) noexcept;
[[nodiscard]] r30_reference_factor
r30_reference_factor_at(std::uint8_t, std::uint8_t) noexcept;
[[nodiscard]] r30_reference_point
r30_reference_lattice_point(std::uint8_t, std::uint8_t, std::int32_t,
                            std::int32_t) noexcept;
[[nodiscard]] r30_reference_subset
r30_reference_subset_at(std::uint8_t) noexcept;
[[nodiscard]] r30_reference_pair r30_reference_pair_at(std::uint8_t) noexcept;

} // namespace holonics::tests
