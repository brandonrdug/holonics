#include "r5_verify.hpp"

#include <cstddef>

namespace holonics::tests {
namespace {

bool equal(const current::sparse_current& left, const current::sparse_current& right) noexcept {
  return left.occurrence == right.occurrence && left.lineage == right.lineage &&
      left.local_state == right.local_state && left.caused_support == right.caused_support &&
      left.site == right.site && left.phase == right.phase &&
      left.multiplicity == right.multiplicity && left.component == right.component &&
      left.open == right.open;
}

bool equal(const current::morphology_cell& left,
    const current::morphology_cell& right) noexcept {
  return left.scale == right.scale && left.offset == right.offset &&
      left.passages == right.passages;
}

bool equal(const current::current_delta& left, const current::current_delta& right) noexcept {
  return left.predecessor == right.predecessor && left.input_event == right.input_event &&
      left.return_event == right.return_event && left.read_support == right.read_support &&
      left.change_support == right.change_support &&
      left.incidence_delta == right.incidence_delta &&
      left.morphology_delta == right.morphology_delta &&
      left.successor_current == right.successor_current &&
      left.returned_consequence == right.returned_consequence && left.stress == right.stress &&
      left.obstruction == right.obstruction && left.logical_resource == right.logical_resource &&
      left.lineage == right.lineage && left.source_site == right.source_site &&
      left.successor_count == right.successor_count;
}

bool equal(const current::front_receipt& left, const current::front_receipt& right) noexcept {
  return left.predecessor == right.predecessor && left.successor == right.successor &&
      left.event_first == right.event_first && left.read_support == right.read_support &&
      left.change_support == right.change_support && left.current_fold == right.current_fold &&
      left.input_count == right.input_count && left.output_count == right.output_count &&
      left.reservations == right.reservations && left.pending_before == right.pending_before &&
      left.pending_after == right.pending_after;
}

bool equal(const current::component_quiescence& left,
    const current::component_quiescence& right) noexcept {
  return left.local_current == right.local_current && left.in_flight == right.in_flight &&
      left.certified == right.certified;
}

std::size_t observation_failures(const current::causal_program& program,
    const current::current_observation& actual,
    const current::current_observation& oracle) noexcept {
  std::size_t failures = 0;
  failures += actual.program_identity != oracle.program_identity;
  failures += actual.predecessor != oracle.predecessor;
  failures += actual.successor != oracle.successor;
  failures += actual.receiver_support != oracle.receiver_support;
  failures += actual.touched_support != oracle.touched_support;
  failures += actual.state != oracle.state;
  failures += actual.obstruction != oracle.obstruction;
  failures += actual.front_count != oracle.front_count;
  failures += actual.final_current_count != oracle.final_current_count;
  failures += actual.local_pending_count != oracle.local_pending_count;
  failures += actual.delta_count != oracle.delta_count;
  failures += actual.compositional_quiescence != oracle.compositional_quiescence;
  failures += actual.source_detached != oracle.source_detached;
  for (std::size_t slot = 0; slot < actual.front_count; ++slot) {
    failures += !equal(actual.fronts[slot], oracle.fronts[slot]);
  }
  for (std::size_t slot = 0; slot < program.component_count; ++slot) {
    failures += !equal(actual.components[slot], oracle.components[slot]);
  }
  for (std::size_t slot = 0; slot < actual.final_current_count; ++slot) {
    failures += !equal(actual.final_currents[slot], oracle.final_currents[slot]);
  }
  for (std::size_t slot = 0; slot < program.site_count; ++slot) {
    failures += !equal(actual.morphology[slot], oracle.morphology[slot]);
  }
  for (std::size_t slot = 0; slot < actual.delta_count; ++slot) {
    failures += !equal(actual.deltas[slot], oracle.deltas[slot]);
  }
  failures += (actual.touched_support.value() & ~actual.receiver_support.value()) != 0;
  failures += !actual.source_detached;
  return failures;
}

}  // namespace

std::size_t r5_verification_failures(
    const current::current_mount_batch& mount,
    const apparatus::causal_current_executor_receipt& execution,
    const current::current_batch_observation& actual,
    const current::current_batch_observation& oracle,
    const apparatus::causal_current_executor_receipt& unavailable) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned();
  failures += execution.kernel_launches != exact::word{3};
  failures += execution.host_semantic_candidates != exact::word{0};
  failures += execution.host_oracle_replays != exact::word{0};
  failures += actual.count != mount.count || oracle.count != mount.count;
  for (std::size_t slot = 0; slot < mount.count; ++slot) {
    failures += observation_failures(mount.programs[slot], actual.cases[slot], oracle.cases[slot]);
  }
  failures += actual.cases[0].state != current::current_status::exact_rest;
  failures += !actual.cases[0].compositional_quiescence;
  failures += actual.cases[1].state != current::current_status::exact_rest;
  failures += !actual.cases[1].compositional_quiescence;
  failures += actual.cases[2].state != current::current_status::open_frontier;
  failures += actual.cases[2].final_current_count != 1;
  failures += !actual.cases[2].final_currents[0].open;
  failures += actual.cases[3].state != current::current_status::obstructed;
  failures += actual.cases[3].obstruction != current::current_obstruction::arithmetic_overflow;
  failures += actual.cases[3].successor != actual.cases[3].predecessor;
  failures += actual.cases[3].morphology[0].passages != exact::word{0};
  failures += unavailable.state != apparatus::causal_current_executor_status::device_unavailable;
  failures += unavailable.obstruction != current::current_obstruction::device_unavailable;
  failures += unavailable.kernel_launches != exact::word{0};
  failures += unavailable.host_oracle_replays != exact::word{0};
  return failures;
}

}  // namespace holonics::tests
