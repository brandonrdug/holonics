#pragma once

#include <cstdint>

namespace holonics::tests {

struct r11_expected final {
  std::uint64_t declaration_ids[7]{};
  std::uint16_t declaration_count{};
  std::uint16_t dependency_count{};
  std::uint16_t transport_alternatives{};
  std::uint16_t substitutions{};
  std::uint64_t intersection_type{};
  std::uint64_t proof_term{};
};

[[nodiscard]] r11_expected r11_oracle() noexcept;

}  // namespace holonics::tests
