#include "r8_oracle.hpp"

#include <cstddef>

namespace holonics::tests {
namespace {

receiver::condensed_snapshot snapshot(const receiver::condensation_program& program,
    const std::uint64_t* values,
    std::uint64_t head,
    std::uint64_t morphology,
    std::uint64_t current,
    std::uint64_t lineage,
    std::uint64_t resource) noexcept {
  receiver::condensed_snapshot result{};
  result.head = exact::word{head};
  result.incidence = program.incidence;
  result.morphology = exact::word{morphology};
  result.current = exact::word{current};
  result.lineage = exact::word{lineage};
  result.logical_resource = exact::word{resource};
  result.alternatives = program.alternatives;
  result.source_count = program.source_count;
  for (std::size_t slot = 0; slot < program.source_count; ++slot) {
    result.source_identities[slot] = program.source_identities[slot];
    result.source_values[slot] = exact::word{values[slot]};
  }
  return result;
}

void fill_step(receiver::boundary_bisimulation_step& step,
    const receiver::condensation_program& program,
    std::size_t history,
    const std::uint64_t* values,
    std::uint64_t predecessor,
    std::uint64_t morphology,
    std::uint64_t response,
    std::uint64_t lineage,
    std::uint64_t resource,
    std::uint16_t factors) noexcept {
  const auto& input = program.history[history];
  const auto& family = history < program.refinement_after_history ?
      program.initial_family : program.refined_family;
  step.input_occurrence = input.occurrence;
  step.input_port = input.port;
  step.common_predecessor = exact::word{predecessor};
  step.direct_input_language = family.admitted_input_support;
  step.condensed_input_language = family.admitted_input_support;
  step.response = {family.identity, family.version, exact::word{input.query},
      exact::word{response}, exact::word{response}, family.admitted_input_support,
      factors, true};
  const auto successor = snapshot(program, values, predecessor + 1U,
      morphology, response, lineage, resource);
  step.direct_successor = successor;
  step.condensed_successor = successor;
  step.next_language_equal = true;
  step.testimony_equal = true;
  step.obstruction_equal = true;
  step.incidence_equal = true;
  step.current_equal = true;
  step.morphology_equal = true;
  step.alternatives_equal = true;
  step.lineage_equal = true;
  step.logical_resource_equal = true;
  step.complete_successor_equal = true;
}

}  // namespace

apparatus::boundary_condensation_observation r8_oracle(
    const apparatus::boundary_condensation_mount& mount) noexcept {
  apparatus::boundary_condensation_observation result{};
  auto& output = result.semantic;
  const auto& program = mount.program;
  std::uint64_t values[8]{2, 3, 5, 7, 11, 13, 17, 19};
  output.program_identity = program.identity;
  output.predecessor = snapshot(program, values, 8'001'000, 10, 0, 100, 0);
  values[1] = 5;
  fill_step(output.history[0], program, 0, values, 8'001'000, 12, 182, 101, 1, 3);
  values[4] = 14;
  fill_step(output.history[1], program, 1, values, 8'001'001, 15, 434, 103, 2, 3);
  output.refinement.occurrence = program.refinement_occurrence;
  output.refinement.predecessor = exact::word{8'001'002};
  output.refinement.successor = exact::word{8'001'003};
  output.refinement.old_family = program.initial_family.identity;
  output.refinement.old_version = program.initial_family.version;
  output.refinement.new_family = program.refined_family.identity;
  output.refinement.new_version = program.refined_family.version;
  output.refinement.reconstruction_capability = program.reconstruction_capability;
  output.refinement.lineage = program.refinement_lineage;
  output.refinement.old_group_count = 3;
  output.refinement.new_group_count = 4;
  output.refinement.family_grew = true;
  output.refinement.source_reopened = true;
  output.refinement.exact_reconstruction = true;
  output.refinement.retained_fiber = true;
  values[0] = 7;
  fill_step(output.history[2], program, 2, values, 8'001'003, 20, 795, 116, 4, 4);
  values[7] = 26;
  fill_step(output.history[3], program, 3, values, 8'001'004, 27, 214, 120, 5, 4);
  output.successor = snapshot(program, values, 8'001'005, 27, 214, 120, 5);
  output.history_count = 4;
  output.factorized_boundary = true;
  output.stateful_bisimulation = true;
  output.source_fiber_retained = true;
  output.non_resumable = true;
  return result;
}

}  // namespace holonics::tests
