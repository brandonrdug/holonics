#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::receiver {

struct theorem_production_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word target_type{};
  exact::word metavariable{};
  std::uint16_t maximum_dependencies{};
};

struct dependent_theorem_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word required_returned_fiber{};
  exact::word target_type{};
  std::uint16_t maximum_dependencies{};
};

}  // namespace holonics::receiver
