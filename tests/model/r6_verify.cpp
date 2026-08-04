#include "r6_verify.hpp"

#include <cstddef>

namespace holonics::tests {
namespace {

bool equal(const current::weave_cell& left, const current::weave_cell& right) noexcept {
  return left.identity == right.identity && left.value == right.value &&
      left.morphology == right.morphology && left.current == right.current &&
      left.lineage == right.lineage && left.placement == right.placement &&
      left.aperture == right.aperture;
}

bool equal(const current::weave_snapshot& left,
    const current::weave_snapshot& right) noexcept {
  if (left.head != right.head || left.incidence != right.incidence ||
      left.lineage_order != right.lineage_order || left.obstruction != right.obstruction ||
      left.cell_count != right.cell_count || left.event_count != right.event_count ||
      left.logical.capacity != right.logical.capacity || left.logical.used != right.logical.used) {
    return false;
  }
  for (std::size_t slot = 0; slot < left.cell_count; ++slot) {
    if (!equal(left.cells[slot], right.cells[slot])) { return false; }
  }
  for (std::size_t slot = 0; slot < left.event_count; ++slot) {
    if (left.emitted[slot] != right.emitted[slot] ||
        left.logical.reservations[slot] != right.logical.reservations[slot]) {
      return false;
    }
  }
  return true;
}

bool equal(const current::weave_delta& left, const current::weave_delta& right) noexcept {
  return left.predecessor == right.predecessor && left.event == right.event &&
      left.input_port == right.input_port && left.output_port == right.output_port &&
      left.read_support == right.read_support && left.change_support == right.change_support &&
      left.value_delta == right.value_delta &&
      left.morphology_delta == right.morphology_delta &&
      left.successor_current == right.successor_current &&
      left.consequence == right.consequence && left.stress == right.stress &&
      left.obstruction == right.obstruction &&
      left.logical_resource == right.logical_resource && left.lineage == right.lineage &&
      left.interaction == right.interaction && left.cell == right.cell;
}

bool equal(const current::resource_backreaction_receipt& left,
    const current::resource_backreaction_receipt& right) noexcept {
  return left.returned.occurrence == right.returned.occurrence &&
      left.returned.port == right.returned.port && left.returned.lineage == right.returned.lineage &&
      left.returned.available_bytes == right.returned.available_bytes &&
      left.returned.resident_bytes == right.returned.resident_bytes &&
      left.returned.temperature_upper_millikelvin ==
          right.returned.temperature_upper_millikelvin &&
      left.policy.expected_port == right.policy.expected_port &&
      left.policy.required_bytes == right.policy.required_bytes &&
      left.policy.temperature_limit_millikelvin ==
          right.policy.temperature_limit_millikelvin &&
      left.policy.alternative_partition == right.policy.alternative_partition &&
      left.policy.alternative_aperture == right.policy.alternative_aperture &&
      left.policy.alternative_declared == right.policy.alternative_declared &&
      left.predecessor_head == right.predecessor_head &&
      left.successor_head == right.successor_head && left.obstruction == right.obstruction &&
      left.partition_before == right.partition_before &&
      left.partition_after == right.partition_after &&
      left.aperture_before == right.aperture_before &&
      left.aperture_after == right.aperture_after && left.retry_count == right.retry_count &&
      left.pressure_returned == right.pressure_returned &&
      left.morphology_changed == right.morphology_changed &&
      left.remained_open == right.remained_open;
}

std::size_t certificate_failures(const current::weave_program& program,
    const current::weave_semantic_observation& semantic) noexcept {
  std::size_t failures = 0;
  const auto& serial = semantic.serial;
  failures += serial.common_predecessor != program.predecessor;
  failures += serial.first_event != program.events[0].identity;
  failures += serial.second_event != program.events[1].identity;
  failures += serial.first_output_port != serial.second_input_port;
  failures += !serial.port_typed || !serial.lineage_retained || !serial.chronology_retained;
  const auto& parallel = semantic.parallel;
  failures += parallel.common_predecessor != program.predecessor;
  failures += parallel.left_event != program.events[2].identity;
  failures += parallel.right_event != program.events[3].identity;
  failures += !parallel.identity_equal || !parallel.causal_order_equal ||
      !parallel.incidence_equal || !parallel.morphology_equal || !parallel.current_equal ||
      !parallel.consequence_equal || !parallel.obstruction_equal ||
      !parallel.logical_resource_equal || !parallel.complete_successor_equal;
  failures += !equal(parallel.left_right, parallel.right_left);
  failures += !equal(parallel.left_right, parallel.canonical);
  failures += parallel.left_right.head != exact::word{program.predecessor.value() + 1U};
  failures += parallel.left_right.cells[2].value !=
      exact::word{program.cells[2].value.value() + program.events[2].value_delta.value()};
  failures += parallel.left_right.cells[3].value !=
      exact::word{program.cells[3].value.value() + program.events[3].value_delta.value()};
  failures += parallel.canonical_delta.common_predecessor != program.predecessor;
  failures += parallel.canonical_delta.event_support != exact::word{(1U << 2U) | (1U << 3U)};
  failures += parallel.canonical_delta.logical_resource != exact::word{2};
  for (std::size_t order = 0; order < current::coherence_permutation_capacity; ++order) {
    failures += !equal(semantic.coherence.successors[0],
        semantic.coherence.successors[order]);
  }
  failures += !semantic.coherence.adjacent_interchanges ||
      !semantic.coherence.braid_equal || !semantic.coherence.complete_successors_equal;
  const auto& interaction = semantic.interaction;
  failures += !interaction.compatible || !interaction.equalized;
  failures += interaction.overlap_support != program.events[7].change_support;
  failures += interaction.interaction != program.events[7].interaction;
  failures += interaction.combined_value_delta != exact::word{52};
  failures += interaction.combined_current != exact::word{2'015};
  failures += interaction.successor.cells[7].current != interaction.combined_current;
  failures += !semantic.recurrence.repeated_support;
  failures += semantic.recurrence.complete_state_recurrence;
  failures += semantic.recurrence.first_standing.head == semantic.recurrence.second_standing.head;
  failures += semantic.unproved_overlap.overlap.value() == 0;
  failures += semantic.unproved_overlap.interaction_declared;
  failures += !semantic.unproved_overlap.remained_ordered;
  failures += semantic.unproved_overlap.obstruction != current::weave_obstruction::unproved_overlap;
  return failures;
}

std::size_t case_failures(const current::weave_program& program,
    const apparatus::weave_case_observation& actual,
    const apparatus::weave_case_observation& oracle,
    std::size_t case_slot) noexcept {
  std::size_t failures = 0;
  failures += actual.semantic.program_identity != oracle.semantic.program_identity;
  failures += !equal(actual.semantic.predecessor, oracle.semantic.predecessor);
  failures += !equal(actual.semantic.successor, oracle.semantic.successor);
  failures += actual.semantic.delta_count != oracle.semantic.delta_count;
  failures += actual.semantic.committed_layers != oracle.semantic.committed_layers;
  failures += actual.semantic.canonical_commit != oracle.semantic.canonical_commit;
  for (std::size_t slot = 0; slot < actual.semantic.delta_count; ++slot) {
    failures += !equal(actual.semantic.deltas[slot], oracle.semantic.deltas[slot]);
  }
  failures += !equal(actual.semantic.resource, oracle.semantic.resource);
  failures += actual.partition_successors_equal != oracle.partition_successors_equal;
  failures += actual.completion_successors_equal != oracle.completion_successors_equal;
  for (std::size_t variant = 0; variant < current::weave_variant_capacity; ++variant) {
    failures += actual.variants[variant].partition_count !=
        oracle.variants[variant].partition_count;
    failures += actual.variants[variant].completion_order !=
        oracle.variants[variant].completion_order;
    failures += actual.variants[variant].non_resumable != oracle.variants[variant].non_resumable;
    failures += !equal(actual.variants[variant].successor,
        oracle.variants[variant].successor);
  }
  failures += !actual.partition_successors_equal || !actual.completion_successors_equal;
  failures += !actual.semantic.canonical_commit;
  failures += actual.semantic.resource.retry_count != 0;
  if (case_slot == 0) {
    failures += !actual.semantic.resource.morphology_changed;
    failures += actual.semantic.resource.remained_open;
    failures += actual.semantic.successor.cells[0].placement != 2;
    failures += actual.semantic.successor.cells[0].aperture != 4;
  } else {
    failures += actual.semantic.resource.morphology_changed;
    failures += !actual.semantic.resource.remained_open;
    failures += actual.semantic.successor.obstruction !=
        current::weave_obstruction::returned_resource_open;
    failures += actual.semantic.successor.cells[0].placement != 1;
  }
  failures += certificate_failures(program, actual.semantic);
  return failures;
}

}  // namespace

std::size_t r6_verification_failures(const current::weave_mount_batch& mount,
    const apparatus::weave_executor_receipt& execution,
    const apparatus::weave_batch_observation& actual,
    const apparatus::weave_batch_observation& oracle) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned();
  failures += execution.kernel_launches != exact::word{3};
  failures += execution.host_semantic_events != exact::word{0};
  failures += execution.unchanged_retries != exact::word{0};
  failures += actual.count != mount.count || oracle.count != mount.count;
  for (std::size_t slot = 0; slot < mount.count; ++slot) {
    failures += case_failures(mount.programs[slot], actual.cases[slot], oracle.cases[slot], slot);
  }
  return failures;
}

}  // namespace holonics::tests
