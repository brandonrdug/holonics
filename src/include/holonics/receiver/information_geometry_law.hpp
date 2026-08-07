#pragma once

#include <cstdint>

#include <holonics/receiver/geometry_exact.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr information_geometry_receipt
    receive_information_geometry(const information_geometry_program& program,
        exact::word standing_head,
        exact::word current_before,
        exact::word returned_stress,
        bool complete_state_recurrence) noexcept {
  information_geometry_receipt result{};
  std::uint64_t time_square = 0;
  std::uint64_t space_square = 0;
  std::uint64_t time_weight = 0;
  std::uint64_t space_weight = 0;
  std::uint64_t positive = 0;
  std::uint64_t negative = 0;
  std::uint64_t denominator = 0;
  if (!geometry_multiply(program.delta_time.value(), program.delta_time.value(), time_square) ||
      !geometry_multiply(program.delta_space.value(), program.delta_space.value(), space_square) ||
      !geometry_multiply(time_square, program.metric[0].first.value(), time_weight) ||
      !geometry_multiply(space_square, program.metric[1].first.value(), space_weight) ||
      !geometry_multiply(time_weight, program.metric[1].second.value(), positive) ||
      !geometry_multiply(space_weight, program.metric[0].second.value(), negative) ||
      !geometry_multiply(program.metric[0].second.value(),
          program.metric[1].second.value(), denominator) || denominator == 0) {
    return result;
  }
  const auto interval = geometry_signed_difference(positive, negative);
  result.interval_magnitude = interval.magnitude;
  result.interval_denominator = exact::word{denominator};
  result.metric[0] = program.metric[0];
  result.metric[1] = program.metric[1];
  result.interval_negative = interval.negative;
  result.causal_accessible = !interval.negative && program.first_support.value() != 0;
  result.metric_declared = program.metric[0].second.value() != 0 &&
      program.metric[1].second.value() != 0;
  result.receiver_clocks[0] = program.receiver_clocks[0];
  result.receiver_clocks[1] = program.receiver_clocks[1];
  std::uint64_t left = 0;
  std::uint64_t right = 0;
  result.receiver_clocks_distinct =
      geometry_multiply(program.receiver_clocks[0].first.value(),
          program.receiver_clocks[1].second.value(), left) &&
      geometry_multiply(program.receiver_clocks[0].second.value(),
          program.receiver_clocks[1].first.value(), right) && left != right;
  result.current_before = current_before;
  std::uint64_t current_after = 0;
  if (!geometry_add(current_before.value(), program.connection_delta.value(), current_after)) {
    return {};
  }
  result.current_after = exact::word{current_after};
  result.carried_phase = program.carried_phase;
  result.returned_stress = returned_stress;
  result.first_support = program.first_support;
  result.second_support = program.second_support;
  result.standing_head = standing_head;
  result.missing_relativistic_obligations = program.missing_relativistic_obligations;
  result.connection_declared = program.connection_delta.value() != 0;
  result.repeated_support = program.first_support == program.second_support;
  result.complete_state_recurrence = complete_state_recurrence;
  result.accelerometer_domain_relative = program.accelerometer_domain.value() != 0;
  result.cycle_domain_relative = program.cycle_domain.value() != 0 &&
      program.cycle_domain != program.accelerometer_domain;
  result.general_relativistic_fidelity =
      program.missing_relativistic_obligations.value() == 0;
  return result;
}

}  // namespace holonics::receiver
