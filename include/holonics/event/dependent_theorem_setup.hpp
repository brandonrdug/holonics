#pragma once

#include <cstddef>
#include <cstdint>
#include <type_traits>

#include <holonics/receiver/theorem_production_question.hpp>

namespace holonics::event {

struct dependent_theorem_setup final {
  receiver::dependent_theorem_question question{};
  exact::word statement{};
  exact::word proof{};
  exact::word passage{};
  exact::word selected_route{};
  exact::word predicted_consequence{};
  std::uint16_t dependency_count{};
  bool frozen{};
  bool complete_source_absent{};
  bool factors_through_returned_fiber{};
  std::uint64_t integrity{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t dependent_setup_integrity(
    const dependent_theorem_setup& setup) noexcept {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  const std::uint64_t values[13]{setup.question.identity.value(),
      setup.question.receiver.value(), setup.question.required_returned_fiber.value(),
      setup.question.target_type.value(), setup.question.maximum_dependencies,
      setup.statement.value(), setup.proof.value(), setup.passage.value(),
      setup.selected_route.value(), setup.predicted_consequence.value(),
      setup.dependency_count, setup.frozen ? 1U : 0U,
      setup.factors_through_returned_fiber ? 1U : 0U};
  for (const auto value : values) {
    std::uint64_t remainder = value;
    for (std::size_t octet = 0; octet < 8; ++octet) {
      fold ^= remainder & 255U;
      fold *= prime;
      remainder >>= 8U;
    }
  }
  fold ^= setup.complete_source_absent ? 1U : 0U;
  fold *= prime;
  return fold;
}

static_assert(std::is_trivially_copyable_v<dependent_theorem_setup>);

}  // namespace holonics::event
