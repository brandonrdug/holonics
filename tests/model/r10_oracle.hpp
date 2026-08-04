#pragma once

#include <cstdint>

namespace holonics::tests {
struct r10_expected final {
  std::uint64_t predecessor{};
  std::uint64_t continuation{};
  std::uint64_t successor{};
  std::uint64_t ablation_body{};
  std::uint64_t exposure_response{};
  std::uint64_t before_response{};
  std::uint64_t before_obstruction{};
  std::uint64_t after_response{};
  std::uint64_t after_transport{};
  std::uint64_t after_codec{};
  std::uint64_t region_morphology{};
  std::uint64_t region_current{};
};
[[nodiscard]] r10_expected r10_oracle() noexcept;
}  // namespace holonics::tests
