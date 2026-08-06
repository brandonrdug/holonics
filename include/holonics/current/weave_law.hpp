#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/current/weave_receipt.hpp>

namespace holonics::current {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool weave_add(
    std::uint64_t left,
    std::uint64_t right,
    std::uint64_t& sum) noexcept {
  if (left > ~std::uint64_t{0} - right) { return false; }
  sum = left + right;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr weave_obstruction validate_weave_program(
    const weave_program& program) noexcept {
  if (program.identity.value() == 0 || program.predecessor.value() == 0 ||
      program.incidence.value() == 0 || program.lineage_seed.value() == 0 ||
      program.cell_count == 0 || program.cell_count > weave_cell_capacity ||
      program.event_count == 0 || program.event_count > weave_event_capacity ||
      program.interaction_left >= program.event_count ||
      program.interaction_right >= program.event_count ||
      program.recurrence_first >= program.event_count ||
      program.recurrence_second >= program.event_count ||
      program.layer_count == 0 || program.layer_count > weave_layer_capacity ||
      program.resource.expected_port.value() == 0 ||
      program.returned_resource.port != program.resource.expected_port) {
    return weave_obstruction::invalid_program;
  }
  std::uint64_t logical_total = 0;
  std::uint64_t value_totals[weave_cell_capacity]{};
  std::uint64_t morphology_totals[weave_cell_capacity]{};
  std::size_t layered_events = 0;
  for (std::size_t layer = 0; layer < program.layer_count; ++layer) {
    if (program.layer_offsets[layer] != layered_events || program.layer_counts[layer] == 0 ||
        program.layer_counts[layer] > program.event_count - layered_events) {
      return weave_obstruction::invalid_program;
    }
    const std::size_t offset = program.layer_offsets[layer];
    const std::size_t count = program.layer_counts[layer];
    for (std::size_t left = 0; left < count; ++left) {
      for (std::size_t right = left + 1; right < count; ++right) {
        const std::size_t first = offset + left;
        const std::size_t second = offset + right;
        const bool declared_interaction =
            first == program.interaction_left && second == program.interaction_right;
        const std::uint64_t overlap = (program.events[first].read_support.value() |
            program.events[first].change_support.value()) &
            (program.events[second].read_support.value() |
                program.events[second].change_support.value());
        if (overlap != 0 && !declared_interaction) {
          return weave_obstruction::unproved_overlap;
        }
      }
    }
    layered_events += program.layer_counts[layer];
  }
  if (layered_events != program.event_count) { return weave_obstruction::invalid_program; }
  for (std::size_t cell = 0; cell < program.cell_count; ++cell) {
    if (program.cells[cell].identity.value() == 0 || program.cells[cell].aperture == 0) {
      return weave_obstruction::invalid_program;
    }
  }
  for (std::size_t slot = 0; slot < program.event_count; ++slot) {
    const auto& event = program.events[slot];
    if (event.identity.value() == 0 || event.input_port.value() == 0 ||
        event.output_port.value() == 0 || event.lineage.value() == 0 ||
        event.read_support.value() == 0 || event.change_support.value() == 0 ||
        event.cell >= program.cell_count ||
        !weave_add(logical_total, event.logical_resource.value(), logical_total)) {
      return weave_obstruction::invalid_program;
    }
    if (!weave_add(value_totals[event.cell], event.value_delta.value(),
            value_totals[event.cell]) ||
        !weave_add(morphology_totals[event.cell], event.admitted_tally_delta.value(),
            morphology_totals[event.cell])) {
      return weave_obstruction::invalid_program;
    }
  }
  if (logical_total > program.logical_capacity.value() ||
      program.logical_capacity.value() == 0) {
    return weave_obstruction::logical_resource_refused;
  }
  for (std::size_t cell = 0; cell < program.cell_count; ++cell) {
    std::uint64_t admitted = 0;
    if (!weave_add(program.cells[cell].value.value(), value_totals[cell], admitted) ||
        !weave_add(program.cells[cell].morphology.value(), morphology_totals[cell], admitted)) {
      return weave_obstruction::invalid_program;
    }
  }
  if (program.events[0].output_port != program.events[1].input_port ||
      program.events[program.interaction_left].interaction.value() == 0 ||
      program.events[program.interaction_left].interaction !=
          program.events[program.interaction_right].interaction ||
      program.events[program.interaction_left].cell !=
          program.events[program.interaction_right].cell ||
      program.events[program.recurrence_first].change_support !=
          program.events[program.recurrence_second].change_support ||
      (program.unproved_left_support.value() & program.unproved_right_support.value()) == 0) {
    return weave_obstruction::invalid_program;
  }
  for (std::size_t variant = 0; variant < weave_variant_capacity; ++variant) {
    bool seen[weave_event_capacity]{};
    std::uint16_t serial_first = weave_event_capacity;
    std::uint16_t serial_second = weave_event_capacity;
    std::uint16_t recurrent = weave_event_capacity;
    for (std::size_t position = 0; position < program.event_count; ++position) {
      const std::uint16_t event = program.variant_orders[variant][position];
      if (event >= program.event_count || seen[event]) { return weave_obstruction::invalid_program; }
      seen[event] = true;
      if (event == 0) { serial_first = static_cast<std::uint16_t>(position); }
      if (event == 1) { serial_second = static_cast<std::uint16_t>(position); }
      if (event == program.recurrence_second) {
        recurrent = static_cast<std::uint16_t>(position);
      }
    }
    if (serial_first >= serial_second || serial_first >= recurrent ||
        program.variant_partitions[variant] == 0) {
      return weave_obstruction::invalid_program;
    }
  }
  return weave_obstruction::none;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr weave_snapshot predecessor_snapshot(
    const weave_program& program) noexcept {
  weave_snapshot result{};
  result.head = program.predecessor;
  result.incidence = program.incidence;
  result.lineage_order = program.lineage_seed;
  result.cell_count = program.cell_count;
  result.event_count = program.event_count;
  result.logical.capacity = program.logical_capacity;
  for (std::size_t cell = 0; cell < program.cell_count; ++cell) {
    result.cells[cell] = program.cells[cell];
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr weave_delta stage_weave_delta(
    exact::word predecessor,
    const weave_event& event) noexcept {
  return weave_delta{predecessor, event.identity, event.input_port, event.output_port,
      event.read_support, event.change_support, event.value_delta,
      event.admitted_tally_delta, event.successor_current, event.consequence,
      event.stress, exact::word{0}, event.logical_resource, event.lineage,
      event.interaction, event.cell};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr weave_obstruction apply_weave_delta(
    weave_snapshot& standing,
    const weave_delta& delta,
    std::size_t event_slot) noexcept {
  if (delta.predecessor != standing.head || delta.cell >= standing.cell_count ||
      event_slot >= standing.event_count) {
    return weave_obstruction::invalid_program;
  }
  std::uint64_t next_value = 0;
  std::uint64_t next_morphology = 0;
  std::uint64_t next_resource = 0;
  if (!weave_add(standing.cells[delta.cell].value.value(), delta.value_delta.value(), next_value) ||
      !weave_add(standing.cells[delta.cell].morphology.value(),
          delta.admitted_tally_delta.value(), next_morphology) ||
      !weave_add(standing.logical.used.value(),
          delta.logical_resource.value(), next_resource) ||
      next_resource > standing.logical.capacity.value()) {
    return weave_obstruction::logical_resource_refused;
  }
  standing.cells[delta.cell].value = exact::word{next_value};
  standing.cells[delta.cell].morphology = exact::word{next_morphology};
  standing.cells[delta.cell].current = delta.successor_current;
  standing.cells[delta.cell].lineage = delta.lineage;
  standing.emitted[event_slot] = delta.consequence;
  standing.logical.used = exact::word{next_resource};
  standing.logical.reservations[event_slot] = delta.logical_resource;
  return weave_obstruction::none;
}

HOLONICS_CALLABLE constexpr void set_weave_successor_head(
    weave_snapshot& standing,
    std::uint64_t successor) noexcept {
  standing.head = exact::word{successor};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal_cells(
    const weave_snapshot& left,
    const weave_snapshot& right) noexcept {
  if (left.cell_count != right.cell_count) { return false; }
  for (std::size_t slot = 0; slot < left.cell_count; ++slot) {
    const auto& first = left.cells[slot];
    const auto& second = right.cells[slot];
    if (first.identity != second.identity || first.value != second.value ||
        first.morphology != second.morphology || first.current != second.current ||
        first.lineage != second.lineage || first.placement != second.placement ||
        first.aperture != second.aperture) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal_resources(
    const weave_snapshot& left,
    const weave_snapshot& right) noexcept {
  if (left.logical.capacity != right.logical.capacity ||
      left.logical.used != right.logical.used) {
    return false;
  }
  for (std::size_t slot = 0; slot < left.event_count; ++slot) {
    if (left.logical.reservations[slot] != right.logical.reservations[slot]) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal_consequences(
    const weave_snapshot& left,
    const weave_snapshot& right) noexcept {
  if (left.event_count != right.event_count) { return false; }
  for (std::size_t slot = 0; slot < left.event_count; ++slot) {
    if (left.emitted[slot] != right.emitted[slot]) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal_complete_standing(
    const weave_snapshot& left,
    const weave_snapshot& right) noexcept {
  return left.head == right.head && left.incidence == right.incidence &&
      left.lineage_order == right.lineage_order && left.obstruction == right.obstruction &&
      equal_cells(left, right) && equal_resources(left, right) &&
      equal_consequences(left, right);
}

}  // namespace holonics::current
