#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::exact {

/// One spine occurrence crossing the device port.
///
/// The Swing, the standing replacement, and the transition grade are all
/// `constexpr` and device-callable, so the identical law runs on the card and on
/// the host and the two returns are compared for exact equality.
struct spine_deed_input final {
  std::uint64_t composed_identity{};
  std::uint64_t direct_identity{};
  std::uint64_t source{};
  std::uint64_t target{};
  std::uint64_t interface_capability{};
  std::uint64_t standing_winding{};
  std::uint64_t receiver{};
  std::uint64_t winding_quantum{};
  std::uint8_t declaration{};
  std::uint8_t projection{};
  bool hand_residual{};
  bool body_layer{};
};

struct spine_deed_output final {
  std::uint8_t disposition{};
  std::uint8_t refusal_state{};
  std::uint64_t winding{};
  std::uint64_t next_groove{};
  std::uint32_t standing_nodes{};
  std::uint32_t path_copied{};
  std::uint32_t population_before{};
  std::uint32_t population_after{};
  std::uint8_t grade_satisfied{};
  bool groove_rebased{};
  bool retains_pair{};
  bool may_conclude{};
};

namespace spine_deed_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const spine_deed_output& left,
    const spine_deed_output& right) noexcept {
  return left.disposition == right.disposition &&
      left.refusal_state == right.refusal_state && left.winding == right.winding &&
      left.next_groove == right.next_groove &&
      left.standing_nodes == right.standing_nodes &&
      left.path_copied == right.path_copied &&
      left.population_before == right.population_before &&
      left.population_after == right.population_after &&
      left.grade_satisfied == right.grade_satisfied &&
      left.groove_rebased == right.groove_rebased &&
      left.retains_pair == right.retains_pair &&
      left.may_conclude == right.may_conclude;
}

}  // namespace spine_deed_law
}  // namespace holonics::exact
