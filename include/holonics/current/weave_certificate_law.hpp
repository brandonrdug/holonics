#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/current/weave_law.hpp>

namespace holonics::current {

[[nodiscard]] HOLONICS_CALLABLE constexpr weave_snapshot apply_selected_events(
    const weave_program& program,
    const std::uint16_t* order,
    std::size_t count,
    std::uint64_t successor_offset) noexcept {
  weave_snapshot result = predecessor_snapshot(program);
  bool interaction_left = false;
  bool interaction_right = false;
  for (std::size_t position = 0; position < count; ++position) {
    const std::size_t slot = order[position];
    if (slot >= program.event_count) {
      result.obstruction = weave_obstruction::invalid_program;
      return result;
    }
    const auto delta = stage_weave_delta(program.predecessor, program.events[slot]);
    interaction_left |= slot == program.interaction_left;
    interaction_right |= slot == program.interaction_right;
    const auto state = apply_weave_delta(result, delta, slot);
    if (state != weave_obstruction::none) {
      result.obstruction = state;
      return result;
    }
  }
  if (interaction_left && interaction_right) {
    const auto& left = program.events[program.interaction_left];
    const auto& right = program.events[program.interaction_right];
    result.cells[left.cell].current = exact::word{
        left.successor_current.value() + right.successor_current.value()};
    result.cells[left.cell].lineage = exact::word{left.lineage.value() + right.lineage.value()};
  }
  set_weave_successor_head(result, program.predecessor.value() + successor_offset);
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr restaging_receipt make_restaging(
    const weave_program& program,
    std::size_t first,
    std::size_t second) noexcept {
  const auto& left = program.events[first];
  const auto& right = program.events[second];
  return restaging_receipt{program.predecessor, left.identity, right.identity,
      program.predecessor, exact::word{left.read_support.value() | right.read_support.value()},
      exact::word{left.change_support.value() | right.change_support.value()},
      program.lineage_seed};
}

HOLONICS_CALLABLE constexpr void add_combined_event(
    combined_weave_delta& combined,
    const weave_event& event,
    std::size_t event_slot) noexcept {
  combined.event_support = exact::word{combined.event_support.value() |
      (std::uint64_t{1} << event_slot)};
  combined.read_support = exact::word{combined.read_support.value() | event.read_support.value()};
  combined.change_support = exact::word{
      combined.change_support.value() | event.change_support.value()};
  combined.value_deltas[event.cell] = event.value_delta;
  combined.morphology_deltas[event.cell] = event.morphology_delta;
  combined.successor_currents[event.cell] = event.successor_current;
  combined.consequences[event_slot] = event.consequence;
  combined.stress = exact::word{combined.stress.value() + event.stress.value()};
  combined.logical_resource = exact::word{
      combined.logical_resource.value() + event.logical_resource.value()};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr interchange_certificate make_interchange(
    const weave_program& program,
    std::uint16_t left,
    std::uint16_t right) noexcept {
  interchange_certificate result{};
  const std::uint16_t lr[2]{left, right};
  const std::uint16_t rl[2]{right, left};
  result.common_predecessor = program.predecessor;
  result.left_event = program.events[left].identity;
  result.right_event = program.events[right].identity;
  result.left_then_right[0] = make_restaging(program, left, right);
  result.left_then_right[1] = make_restaging(program, right, left);
  result.right_then_left[0] = make_restaging(program, right, left);
  result.right_then_left[1] = make_restaging(program, left, right);
  result.left_right = apply_selected_events(program, lr, 2, 1);
  result.right_left = apply_selected_events(program, rl, 2, 1);
  result.canonical = result.left_right;
  result.canonical_delta.common_predecessor = program.predecessor;
  result.canonical_delta.lineage_order = program.lineage_seed;
  add_combined_event(result.canonical_delta, program.events[left], left);
  add_combined_event(result.canonical_delta, program.events[right], right);
  result.identity_equal = result.left_right.head == result.right_left.head;
  for (std::size_t cell = 0; cell < program.cell_count; ++cell) {
    result.identity_equal &= result.left_right.cells[cell].identity ==
        result.right_left.cells[cell].identity;
  }
  result.causal_order_equal = result.left_right.lineage_order == result.right_left.lineage_order;
  result.incidence_equal = result.left_right.incidence == result.right_left.incidence;
  result.morphology_equal = true;
  result.current_equal = true;
  for (std::size_t cell = 0; cell < program.cell_count; ++cell) {
    result.morphology_equal &= result.left_right.cells[cell].morphology ==
        result.right_left.cells[cell].morphology;
    result.current_equal &= result.left_right.cells[cell].current ==
        result.right_left.cells[cell].current;
  }
  result.consequence_equal = equal_consequences(result.left_right, result.right_left);
  result.obstruction_equal = result.left_right.obstruction == result.right_left.obstruction;
  result.logical_resource_equal = equal_resources(result.left_right, result.right_left);
  result.complete_successor_equal =
      equal_complete_standing(result.left_right, result.right_left) &&
      equal_complete_standing(result.left_right, result.canonical);
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr higher_coherence_receipt make_higher_coherence(
    const weave_program& program,
    std::uint16_t first,
    std::uint16_t second,
    std::uint16_t third) noexcept {
  higher_coherence_receipt result{};
  result.common_predecessor = program.predecessor;
  result.events[0] = program.events[first].identity;
  result.events[1] = program.events[second].identity;
  result.events[2] = program.events[third].identity;
  const std::uint16_t orders[coherence_permutation_capacity][3]{
      {first, second, third}, {first, third, second}, {second, first, third},
      {second, third, first}, {third, first, second}, {third, second, first}};
  for (std::size_t order = 0; order < coherence_permutation_capacity; ++order) {
    for (std::size_t position = 0; position < 3; ++position) {
      result.orders[order][position] = orders[order][position];
    }
    result.successors[order] = apply_selected_events(program, orders[order], 3, 1);
  }
  result.adjacent_interchanges = true;
  result.braid_equal = equal_complete_standing(result.successors[0], result.successors[5]);
  result.complete_successors_equal = true;
  for (std::size_t order = 1; order < coherence_permutation_capacity; ++order) {
    result.complete_successors_equal &=
        equal_complete_standing(result.successors[0], result.successors[order]);
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr interaction_equalizer_receipt make_interaction(
    const weave_program& program) noexcept {
  interaction_equalizer_receipt result{};
  const auto& left = program.events[program.interaction_left];
  const auto& right = program.events[program.interaction_right];
  result.common_predecessor = program.predecessor;
  result.left_event = left.identity;
  result.right_event = right.identity;
  result.overlap_support = exact::word{left.change_support.value() & right.change_support.value()};
  result.interaction = left.interaction;
  result.compatible = left.interaction.value() != 0 && left.interaction == right.interaction &&
      result.overlap_support.value() != 0;
  if (!result.compatible) { return result; }
  result.combined_value_delta = exact::word{left.value_delta.value() + right.value_delta.value()};
  result.combined_morphology_delta = exact::word{
      left.morphology_delta.value() + right.morphology_delta.value()};
  result.combined_current = exact::word{
      left.successor_current.value() + right.successor_current.value()};
  result.combined_consequence = exact::word{left.consequence.value() + right.consequence.value()};
  result.lineage = exact::word{left.lineage.value() + right.lineage.value()};
  const std::uint16_t order[2]{program.interaction_left, program.interaction_right};
  result.successor = apply_selected_events(program, order, 2, 1);
  result.equalized = result.successor.obstruction == weave_obstruction::none;
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr event::serial_gluing_receipt make_serial_gluing(
    const weave_program& program,
    std::uint16_t first,
    std::uint16_t second) noexcept {
  const auto& left = program.events[first];
  const auto& right = program.events[second];
  event::serial_gluing_receipt result{program.predecessor, left.identity, right.identity,
      left.output_port, right.input_port, exact::word{left.identity.value() + 1U},
      exact::word{left.lineage.value() + right.lineage.value()}, left.change_support};
  result.port_typed = left.output_port == right.input_port;
  result.lineage_retained = result.intermediate_lineage.value() != 0;
  result.chronology_retained = first < second;
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr recurrence_receipt make_recurrence(
    const weave_program& program) noexcept {
  recurrence_receipt result{};
  const std::uint16_t first[1]{program.recurrence_first};
  const std::uint16_t both[2]{program.recurrence_first, program.recurrence_second};
  result.first_event = program.events[first[0]].identity;
  result.second_event = program.events[both[1]].identity;
  result.first_support = program.events[first[0]].change_support;
  result.second_support = program.events[both[1]].change_support;
  result.first_standing = apply_selected_events(program, first, 1, 1);
  result.second_standing = apply_selected_events(program, both, 2, 2);
  result.repeated_support = result.first_support == result.second_support;
  result.complete_state_recurrence =
      equal_complete_standing(result.first_standing, result.second_standing);
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr ordered_overlap_receipt make_unproved_overlap(
    const weave_program& program) noexcept {
  ordered_overlap_receipt result{};
  result.left_support = program.unproved_left_support;
  result.right_support = program.unproved_right_support;
  result.overlap = exact::word{
      result.left_support.value() & result.right_support.value()};
  result.obstruction = weave_obstruction::unproved_overlap;
  result.remained_ordered = result.overlap.value() != 0;
  return result;
}

}  // namespace holonics::current
