#include "r11_verify.hpp"

#include <cstddef>

namespace holonics::tests {

std::size_t r11_verification_failures(
    const apparatus::mathematical_ecology_executor_receipt& execution,
    const apparatus::mathematical_ecology_observation& actual,
    const apparatus::mathematical_source_receipt& original,
    const apparatus::mathematical_source_receipt& relocated,
    bool exact_material,
    bool sources_detached,
    const r11_expected& expected) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned() || execution.kernel_launches != exact::word{3} ||
      execution.launched_threads != exact::word{3} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.source_bytes_after_mount != exact::word{0};
  failures += original.state != apparatus::mathematical_source_status::exact ||
      relocated.state != apparatus::mathematical_source_status::exact ||
      original.source_count != 2 || relocated.source_count != 2 ||
      original.byte_count != 3'761 || relocated.byte_count != 3'761 ||
      original.chunk_aperture != 73 || relocated.chunk_aperture != 127 ||
      original.chunk_count == relocated.chunk_count ||
      original.material_testimony != relocated.material_testimony ||
      original.path_testimony == relocated.path_testimony ||
      original.recognized_declarations != 15 || relocated.recognized_declarations != 15 ||
      !exact_material || !sources_detached;
  failures += actual.canonical_mount != organ::mathematical_obstruction::none ||
      actual.reordered_mount != organ::mathematical_obstruction::none ||
      !actual.storage_order_invariant || !actual.source_detached ||
      !actual.exact_material_comparison || !actual.local_incidence_only ||
      !actual.final_continuations_valid;
  const auto& held = actual.canonical;
  failures += held.obstruction != organ::mathematical_obstruction::none ||
      held.declaration_count != expected.declaration_count ||
      held.dependency_count != expected.dependency_count ||
      held.dependency_joins != expected.dependency_count ||
      held.transport_alternatives != expected.transport_alternatives ||
      held.substitutions != expected.substitutions || held.unknown_count != 1 ||
      held.global_declaration_scans != 0 ||
      held.intersection_type != exact::word{expected.intersection_type} ||
      held.proof_term != exact::word{expected.proof_term} ||
      !held.term_match || !held.constraint_intersection ||
      !held.proof_structurally_closed || !held.inherited_checked_example ||
      !held.goal_open || !held.source_detached || held.theorem_text_used_as_answer ||
      held.body_consumed || held.body_cloned;
  for (std::size_t slot = 0; slot < expected.declaration_count; ++slot) {
    failures += held.declaration_ids[slot] != exact::word{expected.declaration_ids[slot]};
  }
  failures += actual.mismatch.obstruction != organ::mathematical_obstruction::type_mismatch ||
      actual.mismatch.term_match || actual.mismatch.constraint_intersection ||
      actual.mismatch.intersection_type != exact::word{0};
  failures += actual.unsolved.obstruction != organ::mathematical_obstruction::unsolved_goal ||
      !actual.unsolved.goal_open || actual.unsolved.unknown_count != 1 ||
      !actual.unsolved.proof_structurally_closed ||
      actual.unsolved.theorem_text_used_as_answer;
  return failures;
}

}  // namespace holonics::tests
