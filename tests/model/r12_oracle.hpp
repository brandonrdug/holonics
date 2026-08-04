#pragma once

#include <cstdint>

namespace holonics::tests {

struct r12_expected final {
  std::uint64_t statement{};
  std::uint64_t proof{};
  std::uint64_t passage{};
  std::uint64_t predecessor{};
  std::uint64_t successor{};
  std::uint64_t continuation{};
  std::uint64_t conditioning_response{};
  std::uint64_t final_morphology{};
  std::uint64_t final_current{};
  const char* formal_source{};
  const char* explanation{};
};

[[nodiscard]] r12_expected r12_oracle() noexcept;

}  // namespace holonics::tests
