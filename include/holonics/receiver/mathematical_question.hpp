#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::receiver {

struct mathematical_question final {
  exact::word identity{};
  exact::word receiver{};
  std::uint16_t anchor_slot{};
  exact::word target_type{};
  exact::word hypothesis_type{};
  exact::word metavariable{};
  bool request_generated_closure{};
};

}  // namespace holonics::receiver
