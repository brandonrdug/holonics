#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/condensation_receipt.hpp>
#include <holonics/receiver/geometry_exact.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool factorable_family(
    const future_receiver_family& family,
    const std::uint16_t* groups,
    std::size_t source_count,
    std::size_t group_count) noexcept {
  if (family.identity.value() == 0 || family.version.value() == 0 ||
      family.query_count == 0 || family.query_count > condensation_query_capacity ||
      group_count == 0 || group_count > condensation_group_capacity) {
    return false;
  }
  for (std::size_t source = 0; source < source_count; ++source) {
    if (groups[source] >= group_count) { return false; }
    for (std::size_t earlier = 0; earlier < source; ++earlier) {
      if (groups[source] != groups[earlier]) { continue; }
      for (std::size_t query = 0; query < family.query_count; ++query) {
        if (family.query_weights[query][source] !=
            family.query_weights[query][earlier]) {
          return false;
        }
      }
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr condensation_obstruction
    validate_condensation_program(const condensation_program& program) noexcept {
  if (program.identity.value() == 0 || program.predecessor.value() == 0 ||
      program.incidence.value() == 0 || program.lineage.value() == 0 ||
      program.reconstruction_capability.value() == 0 ||
      program.refinement_occurrence.value() == 0 || program.refinement_lineage.value() == 0 ||
      program.source_count == 0 || program.source_count > condensation_source_capacity ||
      program.refinement_after_history == 0 ||
      program.refinement_after_history >= condensation_history_capacity ||
      program.refined_family.version.value() <= program.initial_family.version.value() ||
      program.refined_family.query_count <= program.initial_family.query_count ||
      !factorable_family(program.initial_family, program.initial_groups,
          program.source_count, program.initial_group_count) ||
      !factorable_family(program.refined_family, program.refined_groups,
          program.source_count, program.refined_group_count)) {
    return condensation_obstruction::invalid_program;
  }
  for (std::size_t source = 0; source < program.source_count; ++source) {
    if (program.source_identities[source].value() == 0) {
      return condensation_obstruction::invalid_program;
    }
  }
  for (std::size_t history = 0; history < condensation_history_capacity; ++history) {
    const auto& input = program.history[history];
    const bool refined = history >= program.refinement_after_history;
    const auto& family = refined ? program.refined_family : program.initial_family;
    if (input.occurrence.value() == 0 || input.port.value() == 0 || input.lineage.value() == 0 ||
        input.source_cell >= program.source_count || input.query >= family.query_count ||
        input.required_family_version != family.version ||
        (family.admitted_input_support.value() &
            (std::uint64_t{1} << input.source_cell)) == 0) {
      return condensation_obstruction::invalid_program;
    }
  }
  return condensation_obstruction::none;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal_condensed_snapshot(
    const condensed_snapshot& left,
    const condensed_snapshot& right) noexcept {
  if (left.head != right.head || left.incidence != right.incidence ||
      left.admitted_tally != right.admitted_tally || left.current != right.current ||
      left.lineage != right.lineage || left.logical_resource != right.logical_resource ||
      left.alternatives != right.alternatives || left.obstruction != right.obstruction ||
      left.source_count != right.source_count) {
    return false;
  }
  for (std::size_t slot = 0; slot < left.source_count; ++slot) {
    if (left.source_identities[slot] != right.source_identities[slot] ||
        left.source_values[slot] != right.source_values[slot]) {
      return false;
    }
  }
  return true;
}

}  // namespace holonics::receiver
