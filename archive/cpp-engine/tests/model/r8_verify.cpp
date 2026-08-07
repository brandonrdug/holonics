#include "r8_verify.hpp"

#include <cstddef>

namespace holonics::tests {
namespace {
bool equal(const receiver::condensed_snapshot& left,
    const receiver::condensed_snapshot& right) noexcept {
  if (left.head != right.head || left.incidence != right.incidence ||
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

std::size_t response_failures(const receiver::factorized_boundary_response& left,
    const receiver::factorized_boundary_response& right) noexcept {
  std::size_t failures = 0;
  failures += left.family != right.family || left.version != right.version ||
      left.query != right.query || left.direct != right.direct ||
      left.factorized != right.factorized ||
      left.retained_source_support != right.retained_source_support ||
      left.factor_count != right.factor_count || left.exact != right.exact;
  failures += !left.exact || left.direct != left.factorized;
  return failures;
}

std::size_t step_failures(const receiver::boundary_bisimulation_step& left,
    const receiver::boundary_bisimulation_step& right) noexcept {
  std::size_t failures = 0;
  failures += left.input_occurrence != right.input_occurrence ||
      left.input_port != right.input_port || left.common_predecessor != right.common_predecessor ||
      left.direct_input_language != right.direct_input_language ||
      left.condensed_input_language != right.condensed_input_language;
  failures += response_failures(left.response, right.response);
  failures += !equal(left.direct_successor, right.direct_successor);
  failures += !equal(left.condensed_successor, right.condensed_successor);
  failures += left.direct_obstruction != right.direct_obstruction ||
      left.condensed_obstruction != right.condensed_obstruction;
  failures += left.next_language_equal != right.next_language_equal ||
      left.testimony_equal != right.testimony_equal ||
      left.obstruction_equal != right.obstruction_equal ||
      left.incidence_equal != right.incidence_equal ||
      left.current_equal != right.current_equal ||
      left.alternatives_equal != right.alternatives_equal ||
      left.lineage_equal != right.lineage_equal ||
      left.logical_resource_equal != right.logical_resource_equal ||
      left.complete_successor_equal != right.complete_successor_equal;
  failures += !left.next_language_equal || !left.testimony_equal ||
      !left.obstruction_equal || !left.incidence_equal || !left.current_equal ||
      !left.alternatives_equal || !left.lineage_equal ||
      !left.logical_resource_equal || !left.complete_successor_equal;
  return failures;
}

std::size_t refinement_failures(const receiver::boundary_refinement_receipt& left,
    const receiver::boundary_refinement_receipt& right) noexcept {
  std::size_t failures = 0;
  failures += left.occurrence != right.occurrence || left.predecessor != right.predecessor ||
      left.successor != right.successor || left.old_family != right.old_family ||
      left.old_version != right.old_version || left.new_family != right.new_family ||
      left.new_version != right.new_version ||
      left.reconstruction_capability != right.reconstruction_capability ||
      left.lineage != right.lineage || left.old_group_count != right.old_group_count ||
      left.new_group_count != right.new_group_count || left.family_grew != right.family_grew ||
      left.source_reopened != right.source_reopened ||
      left.exact_reconstruction != right.exact_reconstruction ||
      left.retained_fiber != right.retained_fiber;
  failures += !left.family_grew || !left.source_reopened || !left.exact_reconstruction ||
      !left.retained_fiber || left.new_version.value() <= left.old_version.value() ||
      left.new_group_count <= left.old_group_count;
  return failures;
}

}  // namespace

std::size_t r8_verification_failures(
    const apparatus::boundary_condensation_executor_receipt& execution,
    const apparatus::boundary_condensation_observation& actual,
    const apparatus::boundary_condensation_observation& oracle) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned();
  failures += execution.kernel_launches != exact::word{3};
  failures += execution.host_semantic_events != exact::word{0};
  const auto& left = actual.semantic;
  const auto& right = oracle.semantic;
  failures += left.program_identity != right.program_identity;
  failures += !equal(left.predecessor, right.predecessor);
  failures += !equal(left.successor, right.successor);
  failures += left.obstruction != right.obstruction;
  failures += left.history_count != right.history_count;
  for (std::size_t slot = 0; slot < receiver::condensation_history_capacity; ++slot) {
    failures += step_failures(left.history[slot], right.history[slot]);
  }
  failures += refinement_failures(left.refinement, right.refinement);
  failures += left.factorized_boundary != right.factorized_boundary ||
      left.stateful_bisimulation != right.stateful_bisimulation ||
      left.source_fiber_retained != right.source_fiber_retained ||
      left.non_resumable != right.non_resumable;
  failures += !left.factorized_boundary || !left.stateful_bisimulation ||
      !left.source_fiber_retained || !left.non_resumable;
  return failures;
}

}  // namespace holonics::tests
