#pragma once

#include <holonics/current/interchange_certificate.hpp>
#include <holonics/event/serial_gluing.hpp>

namespace holonics::current {

struct recurrence_receipt final {
  exact::word first_event{};
  exact::word second_event{};
  exact::word first_support{};
  exact::word second_support{};
  weave_snapshot first_standing{};
  weave_snapshot second_standing{};
  bool repeated_support{};
  bool complete_state_recurrence{};
};

struct ordered_overlap_receipt final {
  exact::word left_support{};
  exact::word right_support{};
  exact::word overlap{};
  weave_obstruction obstruction{weave_obstruction::none};
  bool interaction_declared{};
  bool remained_ordered{};
};

struct resource_backreaction_receipt final {
  resource_return returned{};
  resource_policy policy{};
  exact::word predecessor_head{};
  exact::word successor_head{};
  weave_obstruction obstruction{weave_obstruction::none};
  std::uint16_t partition_before{};
  std::uint16_t partition_after{};
  std::uint16_t aperture_before{};
  std::uint16_t aperture_after{};
  std::uint16_t retry_count{};
  bool pressure_returned{};
  bool morphology_changed{};
  bool remained_open{};
};

struct weave_semantic_observation final {
  exact::word program_identity{};
  weave_snapshot predecessor{};
  weave_snapshot successor{};
  weave_delta deltas[weave_event_capacity]{};
  event::serial_gluing_receipt serial{};
  interchange_certificate parallel{};
  higher_coherence_receipt coherence{};
  interaction_equalizer_receipt interaction{};
  recurrence_receipt recurrence{};
  ordered_overlap_receipt unproved_overlap{};
  resource_backreaction_receipt resource{};
  std::uint16_t delta_count{};
  std::uint16_t committed_layers{};
  bool canonical_commit{};
};

}  // namespace holonics::current
