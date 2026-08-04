#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::receiver {

enum class equivalence_orientation : std::uint8_t { forward, reverse };

struct generative_math_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word premise_declaration{};
  exact::word target_type{};
  exact::word metavariable{};
  std::uint16_t maximum_dependencies{};
  equivalence_orientation orientation{equivalence_orientation::forward};
};

}  // namespace holonics::receiver
