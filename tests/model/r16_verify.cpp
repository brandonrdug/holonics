#include "r16_verify.hpp"

namespace holonics::tests {
namespace {

template<std::size_t Capacity, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], std::uint16_t used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return true; }
  }
  return false;
}

}  // namespace

std::size_t r16_verification_failures(
    const apparatus::theorem_rest_store_receipt& rest_load,
    const apparatus::dependent_setup_store_receipt& setup_load,
    apparatus::terminal_store_status first_collection,
    const apparatus::first_return_artifact_testimony& first,
    const apparatus::terminal_theorem_executor_receipt& execution,
    const event::terminal_theorem_observation& actual,
    const event::terminal_theorem_rest_record& handoff) noexcept {
  std::size_t failures = 0;
  failures += !rest_load.returned() || rest_load.bytes != exact::word{200} ||
      rest_load.developmental_source_bytes != exact::word{0} ||
      rest_load.retrieval_handles != exact::word{0} || !rest_load.integrity_exact;
  failures += !setup_load.returned() || setup_load.bytes != exact::word{96} ||
      setup_load.developmental_source_bytes != exact::word{0} ||
      setup_load.retrieval_handles != exact::word{0} || !setup_load.integrity_exact;
  failures += first_collection != apparatus::terminal_store_status::returned || !first.exact ||
      first.deed_bytes == 0 || first.produced_artifact_bytes != 44'440 ||
      first.observer_artifact_reads != exact::word{2} ||
      first.engine_source_reads != exact::word{0};
  failures += !execution.returned() || execution.kernel_launches != exact::word{5} ||
      execution.launched_threads != exact::word{5} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.engine_source_reads != exact::word{0} ||
      execution.exterior_retrieval_calls != exact::word{0} ||
      execution.developmental_source_bytes != exact::word{0} ||
      execution.logical.alternatives_retained != exact::word{1} ||
      execution.logical.obstructions_retained != exact::word{2};
  const auto& process = execution.process;
  failures += !process.returned() || process.exterior_process_calls != exact::word{1} ||
      process.host_semantic_events != exact::word{0} || !process.named_lake_env_lean ||
      !process.raw_bytes_returned || !process.environment.pinned_lean_4_27 ||
      !process.environment.pinned_mathlib_revision || process.source_bytes.value() == 0 ||
      process.produced_artifact_bytes.value() == 0;
  failures += !actual.production_remount.same_body ||
      !actual.production_remount.acquired_return_preserved ||
      actual.production_remount.source_replayed || !actual.source_detached ||
      !actual.setup_integrity_exact || !actual.absent_fiber.exact ||
      actual.absent_fiber.withheld_fiber != exact::word{181'200} ||
      !actual.ablation_remount.same_body || actual.ablation_remount.acquired_return_preserved ||
      actual.ablation_remount.source_replayed || !actual.ablation_generation_refused ||
      actual.ablated_generation.obstruction !=
          organ::theorem_production_obstruction::returned_fiber_absent ||
      actual.ablation_source_bytes != 0 || !actual.dependency_exact;
  const auto& generation = actual.generation;
  failures += generation.obstruction != organ::theorem_production_obstruction::none ||
      generation.goal.identity != exact::word{142'200} ||
      generation.goal.required_returned_fiber != exact::word{181'200} ||
      generation.open_count != 2 || generation.retained_count != 1 ||
      generation.global_candidate_scans != 0 ||
      generation.fibers[0].dependency_count != 2 ||
      generation.fibers[1].dependency_count != 4 ||
      generation.selected.identity != exact::word{182'200} ||
      generation.inherited_passage != exact::word{171'200} ||
      generation.inherited_kernel_return != exact::word{160'200} ||
      generation.inherited_returned_fiber != exact::word{181'200} ||
      generation.passage.identity != exact::word{172'200} ||
      generation.passage.statement != exact::word{152'200} ||
      generation.passage.proof != exact::word{162'200} ||
      generation.passage.selected_rule != exact::word{181'200} ||
      generation.passage.formation != organ::theorem_formation::returned_fiber_extension ||
      !generation.passage.closed || !generation.passage.generated ||
      !generation.exact_local_expansion || !generation.exact_receiver_restriction ||
      !generation.dependency_exact || !generation.proof_current_lineaged;
  failures += generation.exclusion.mounted_answer_matches != 0 ||
      generation.exclusion.lookup_entries != 0 ||
      generation.exclusion.quoted_source_bytes != 0 ||
      generation.exclusion.reference_calls != 0 ||
      generation.exclusion.retained_development_source_bytes != 0 ||
      !generation.exclusion.target_absent_at_mount ||
      !generation.exclusion.source_detached_at_rest;
  failures += actual.generation_commit.state != body::body_change_status::committed ||
      actual.generation_commit.predecessor != exact::word{14'001'002} ||
      actual.generation_commit.successor != exact::word{14'001'003} ||
      actual.generation_commit.admitted_tally_before != 140 ||
      actual.generation_commit.admitted_tally_after != 147;
  failures += actual.formal.passage != exact::word{172'200} ||
      actual.conversational.passage != actual.formal.passage ||
      actual.checker_face.passage != actual.formal.passage ||
      actual.checker_face.generated_source != exact::word{123'203} ||
      actual.checker_face.declaration_form !=
          codec::formal_declaration_form::returned_fiber_extension ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "import R14_GENERATED_TRACE_COMPOSITION") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_trace_rebase_transports_three") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "generated_trace_rebase_transports_composition A e theta") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "(Trace.trans hst htu) huv") || actual.conversational.byte_count == 0;
  failures += actual.checker_stage != event::checker_stage_status::exact ||
      !actual.pending_before_process || actual.pending_after_return ||
      !actual.passage_preserved || actual.outbound.predecessor != exact::word{14'001'003} ||
      actual.outbound.event != exact::word{160'300} ||
      actual.outbound.passage != exact::word{172'200};
  failures += actual.typed.state != event::checker_return_status::accepted ||
      actual.typed.produced_declarations != 1 || actual.typed.remaining_goal_count != 0 ||
      !actual.typed.elaborator_boundary_crossed || !actual.typed.kernel_boundary_crossed ||
      actual.raw.exit_status != 0 || actual.raw.stdout_bytes == 0 ||
      actual.raw.stderr_bytes != 0 || actual.raw.produced_artifact_bytes == 0;
  const auto& morphology = actual.returned_morphology;
  failures += morphology.mathematical_before != 46 || morphology.mathematical_after != 49 ||
      morphology.codec_before != 34 || morphology.codec_after != 36 ||
      morphology.commit.state != body::body_change_status::committed ||
      morphology.commit.predecessor != exact::word{14'001'003} ||
      morphology.commit.successor != exact::word{14'001'004} ||
      morphology.commit.admitted_tally_before != 147 ||
      morphology.commit.admitted_tally_after != 152 || !morphology.returned_difference_applied;
  failures += actual.second_acquired.identity != exact::word{182'200} ||
      actual.second_acquired.passage != exact::word{172'200} ||
      actual.second_acquired.selected_rule != exact::word{181'200} ||
      actual.second_acquired.admitted_tally_delta != exact::word{5} ||
      !actual.second_acquired.accepted;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      actual.rest.retained_source_bytes != 0 || !actual.remount.same_body ||
      !actual.remount.both_returns_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.handoff_continuation_valid ||
      actual.final_head != exact::word{14'001'004} ||
      actual.final_continuation != exact::word{15'001'004};
  failures += handoff.integrity != event::terminal_theorem_rest_integrity(handoff) ||
      handoff.body.head != 14'001'004 || handoff.body.continuation != 15'001'004 ||
      handoff.body.regions[0].admitted_tally != 152 ||
      handoff.first.identity != exact::word{181'200} || !handoff.first.accepted ||
      handoff.second.identity != exact::word{182'200} || !handoff.second.accepted ||
      handoff.mathematical_admitted_tally != 49 || handoff.codec_admitted_tally != 36;
  return failures;
}

}  // namespace holonics::tests
