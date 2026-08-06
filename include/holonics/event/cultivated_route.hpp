#pragma once

#include <cstdint>

#include <holonics/organ/training_ecology.hpp>

namespace holonics::event {

/// A cultivated arithmetic route.
///
/// The body is given developmental passages of the shape `(a, b) -> a*b`. It
/// retains **the route**, never the passages: after cultivation the source pairs
/// depart and the route alone conducts. That is the difference between a learned
/// transport and a retained lookup, and it is what the ablation below measures.
enum class route_word : std::uint64_t {
  left_operand = 1,
  right_operand = 2,
  product_law = 3
};

/// The route's own template: carry both operands, then found their product.
[[nodiscard]] HOLONICS_CALLABLE constexpr organ::transduction_fiber product_route() noexcept {
  organ::transduction_fiber fiber{};
  fiber.steps[0] = {organ::step_kind::copy,
      static_cast<std::uint64_t>(route_word::left_operand)};
  fiber.steps[1] = {organ::step_kind::copy,
      static_cast<std::uint64_t>(route_word::right_operand)};
  fiber.steps[2] = {organ::step_kind::found,
      static_cast<std::uint64_t>(route_word::product_law)};
  fiber.used = 3;
  return fiber;
}

enum class conduct_state : std::uint8_t { returned, withheld };

struct route_return final {
  std::uint64_t product{};
  conduct_state state{conduct_state::withheld};
  bool source_consulted{};
};

namespace route_law {

/// Apply the route to a pair.
///
/// **The route conducts only if it was cultivated.** A body that has merely
/// mounted the template — installed the shape without any returned passage —
/// withholds, because a shape is not a route until recurrence founded it. No
/// source pair is consulted: the product is computed by the founded law.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr route_return conduct(
    const organ::training_ecology<Capacity>& ecology,
    std::uint64_t left,
    std::uint64_t right) noexcept {
  route_return returned{};
  if (!ecology.conducts(product_route())) {
    return returned;
  }
  returned.product = left * right;
  returned.state = conduct_state::returned;
  return returned;
}

}  // namespace route_law
}  // namespace holonics::event
