#include "r12_verify.hpp"

#include <cstddef>

namespace holonics::tests {

bool same_generated_bytes(
    const char* actual, std::size_t actual_count, const char* expected) noexcept {
  std::size_t expected_count = 0;
  while (expected[expected_count] != '\0') { ++expected_count; }
  if (actual_count != expected_count) { return false; }
  for (std::size_t slot = 0; slot < actual_count; ++slot) {
    if (actual[slot] != expected[slot]) { return false; }
  }
  return true;
}

std::size_t r12_verification_failures(
    const apparatus::generative_math_executor_receipt& execution,
    const apparatus::generative_math_observation& actual,
    const r12_expected& expected) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned() || execution.kernel_launches != exact::word{3} ||
      execution.launched_threads != exact::word{3} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.mounted_answer_bytes != exact::word{0} ||
      execution.external_checker_calls != exact::word{0};
  failures += actual.mount_obstruction != organ::generative_obstruction::none;
  const auto& value = actual.returned;
  const auto& generation = value.generation;
  failures += generation.obstruction != organ::generative_obstruction::none ||
      generation.expansion.obstruction != organ::generative_obstruction::receiver_underdetermined ||
      generation.expansion.open_count != 2 ||
      generation.expansion.global_candidate_scans != 0 ||
      generation.expansion.fibers[0].dependency_count != 1 ||
      generation.expansion.fibers[1].dependency_count != 4 ||
      !generation.exact_local_expansion || !generation.exact_receiver_restriction ||
      !generation.proof_current_lineaged || generation.score_used || generation.registry_used;
  failures += generation.passage.statement != exact::word{expected.statement} ||
      generation.passage.proof != exact::word{expected.proof} ||
      generation.passage.identity != exact::word{expected.passage} ||
      generation.passage.premise_declaration != exact::word{112'070} ||
      generation.passage.selected_rule != exact::word{121'010} ||
      generation.passage.formation != organ::proof_formation::equivalence_symmetry ||
      !generation.passage.closed || !generation.passage.generated;
  failures += generation.exclusion.generated_statement != exact::word{expected.statement} ||
      generation.exclusion.generated_proof != exact::word{expected.proof} ||
      generation.exclusion.mounted_answer_matches != 0 ||
      generation.exclusion.lookup_entries != 0 || generation.exclusion.quoted_source_bytes != 0 ||
      !generation.exclusion.distinct_from_inherited ||
      !generation.exclusion.absent_before_generation;
  const auto& information = generation.information;
  failures += information.predecessor != exact::word{expected.predecessor} ||
      information.successor != exact::word{expected.successor} ||
      information.continuation != exact::word{expected.continuation} ||
      information.alternatives_before != 2 || information.alternatives_after != 1 ||
      information.returned_obstruction != organ::generative_obstruction::receiver_underdetermined ||
      !information.obstruction_changed_passage || !information.receiver_indexed ||
      !information.committed;
  failures += value.final_head != exact::word{expected.successor} ||
      value.final_region.morphology != expected.final_morphology ||
      value.final_region.current != expected.final_current || !value.source_detached ||
      !value.same_closed_passage || !value.continuation_valid;
  failures += !same_generated_bytes(value.formal.bytes, value.formal.byte_count,
      expected.formal_source) ||
      !same_generated_bytes(value.conversational.bytes, value.conversational.byte_count,
      expected.explanation) || value.formal.passage != value.conversational.passage;
  return failures;
}

}  // namespace holonics::tests
