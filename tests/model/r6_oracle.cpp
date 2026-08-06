#include "r6_oracle.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

current::weave_snapshot initial(const current::weave_program& program) noexcept {
  current::weave_snapshot result{};
  result.head = program.predecessor;
  result.incidence = program.incidence;
  result.lineage_order = program.lineage_seed;
  result.logical.capacity = program.logical_capacity;
  result.cell_count = program.cell_count;
  result.event_count = program.event_count;
  for (std::size_t cell = 0; cell < program.cell_count; ++cell) {
    result.cells[cell] = program.cells[cell];
  }
  return result;
}

void apply_event(current::weave_snapshot& standing,
    const current::weave_event& event,
    std::size_t slot) noexcept {
  auto& cell = standing.cells[event.cell];
  cell.value = exact::word{cell.value.value() + event.value_delta.value()};
  cell.morphology = exact::word{cell.morphology.value() + event.admitted_tally_delta.value()};
  cell.current = event.successor_current;
  cell.lineage = event.lineage;
  standing.emitted[slot] = event.consequence;
  standing.logical.used = exact::word{
      standing.logical.used.value() + event.logical_resource.value()};
  standing.logical.reservations[slot] = event.logical_resource;
}

void equalize(const current::weave_program& program,
    current::weave_snapshot& standing) noexcept {
  const auto& left = program.events[program.interaction_left];
  const auto& right = program.events[program.interaction_right];
  standing.cells[left.cell].current = exact::word{
      left.successor_current.value() + right.successor_current.value()};
  standing.cells[left.cell].lineage = exact::word{left.lineage.value() + right.lineage.value()};
}

current::weave_snapshot ordered_successor(const current::weave_program& program,
    const std::uint16_t* order,
    std::size_t count,
    std::uint16_t head_steps,
    bool resource) noexcept {
  auto result = initial(program);
  bool left = false;
  bool right = false;
  for (std::size_t position = 0; position < count; ++position) {
    const std::size_t slot = order[position];
    apply_event(result, program.events[slot], slot);
    left |= slot == program.interaction_left;
    right |= slot == program.interaction_right;
  }
  if (left && right) { equalize(program, result); }
  result.head = exact::word{program.predecessor.value() + head_steps};
  if (!resource) { return result; }
  const bool pressure =
      program.returned_resource.available_bytes.value() < program.resource.required_bytes.value() ||
      program.returned_resource.resident_bytes.value() >
          program.returned_resource.available_bytes.value() ||
      program.returned_resource.temperature_upper_millikelvin.value() >
          program.resource.temperature_limit_millikelvin.value();
  if (!pressure) { return result; }
  result.head = exact::word{result.head.value() + 1U};
  if (!program.resource.alternative_declared) {
    result.obstruction = current::weave_obstruction::returned_resource_open;
  } else {
    for (std::size_t cell = 0; cell < result.cell_count; ++cell) {
      result.cells[cell].placement = program.resource.alternative_partition;
      result.cells[cell].aperture = program.resource.alternative_aperture;
    }
  }
  return result;
}

void stage_live_deltas(const current::weave_program& program,
    current::weave_semantic_observation& output) noexcept {
  std::uint64_t head = program.predecessor.value();
  for (std::size_t layer = 0; layer < program.layer_count; ++layer) {
    const std::size_t offset = program.layer_offsets[layer];
    for (std::size_t member = 0; member < program.layer_counts[layer]; ++member) {
      const std::size_t slot = offset + member;
      const auto& event = program.events[slot];
      output.deltas[slot] = {exact::word{head}, event.identity, event.input_port,
          event.output_port, event.read_support, event.change_support, event.value_delta,
          event.admitted_tally_delta, event.successor_current, event.consequence, event.stress,
          exact::word{0}, event.logical_resource, event.lineage, event.interaction, event.cell};
    }
    ++head;
  }
}

void observe_case(const current::weave_program& program,
    apparatus::weave_case_observation& output) noexcept {
  auto& semantic = output.semantic;
  semantic.program_identity = program.identity;
  semantic.predecessor = initial(program);
  semantic.successor = ordered_successor(program, program.variant_orders[0],
      program.event_count, program.layer_count, true);
  semantic.delta_count = program.event_count;
  semantic.committed_layers = static_cast<std::uint16_t>(program.layer_count + 1U);
  semantic.canonical_commit = true;
  stage_live_deltas(program, semantic);
  semantic.resource.returned = program.returned_resource;
  semantic.resource.policy = program.resource;
  semantic.resource.predecessor_head = exact::word{
      program.predecessor.value() + program.layer_count};
  semantic.resource.successor_head = semantic.successor.head;
  semantic.resource.partition_before = program.cells[0].placement;
  semantic.resource.aperture_before = program.cells[0].aperture;
  semantic.resource.pressure_returned = true;
  if (program.resource.alternative_declared) {
    semantic.resource.partition_after = program.resource.alternative_partition;
    semantic.resource.aperture_after = program.resource.alternative_aperture;
    semantic.resource.morphology_changed = true;
  } else {
    semantic.resource.partition_after = semantic.resource.partition_before;
    semantic.resource.aperture_after = semantic.resource.aperture_before;
    semantic.resource.obstruction = current::weave_obstruction::returned_resource_open;
    semantic.resource.remained_open = true;
  }
  output.partition_successors_equal = true;
  output.completion_successors_equal = true;
  for (std::size_t variant = 0; variant < current::weave_variant_capacity; ++variant) {
    output.variants[variant].partition_count = program.variant_partitions[variant];
    output.variants[variant].completion_order = static_cast<std::uint16_t>(variant);
    output.variants[variant].successor = ordered_successor(program,
        program.variant_orders[variant], program.event_count, program.layer_count, true);
    output.variants[variant].non_resumable = true;
  }
}

}  // namespace

apparatus::weave_batch_observation r6_oracle(
    const current::weave_mount_batch& mount) noexcept {
  apparatus::weave_batch_observation output{};
  output.count = mount.count;
  for (std::size_t slot = 0; slot < mount.count; ++slot) {
    observe_case(mount.programs[slot], output.cases[slot]);
  }
  return output;
}

}  // namespace holonics::tests
