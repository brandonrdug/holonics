#pragma once

#include <cstdint>

namespace holonics::tests {

struct r9_expected final {
  std::uint64_t predecessor{};
  std::uint64_t continuation{};
  std::uint64_t successor{};
  std::uint64_t environment{};
  std::uint64_t provenance{};
  std::uint64_t operative{};
  std::uint64_t unrelated{};
  std::uint64_t core_occurrence{};
  std::uint64_t before_core{};
  std::uint64_t before_render_first{};
  std::uint64_t before_transduce_first{};
  std::uint64_t before_transduce_second{};
  std::uint64_t after_core{};
  std::uint64_t after_render_first{};
  std::uint64_t after_transduce_first{};
  std::uint64_t after_transduce_second{};
  std::uint64_t admitted_tally{};
  std::uint64_t current{};
};

[[nodiscard]] r9_expected r9_oracle() noexcept;

}  // namespace holonics::tests
