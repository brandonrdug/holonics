#pragma once

#include <cstdint>

#include <holonics/event/generative_math_return.hpp>
#include <holonics/receiver/generative_math_question.hpp>

namespace holonics::apparatus {

struct generative_math_mount final {
  organ::generative_math_foundation foundation{};
  body::rest_region regions[body::live_region_capacity]{};
  receiver::generative_math_question question{};
  std::uint64_t body_seed{};
};

struct generative_math_observation final {
  organ::generative_obstruction mount_obstruction{organ::generative_obstruction::invalid_foundation};
  event::generative_math_return returned{};
};

}  // namespace holonics::apparatus
