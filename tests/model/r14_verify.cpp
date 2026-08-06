#include "r14_verify.hpp"

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

std::size_t r14_verification_failures(
    const apparatus::theorem_production_executor_receipt& execution,
    const event::theorem_production_observation& actual,
    const event::theorem_production_rest_record& handoff) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned() || execution.kernel_launches != exact::word{5} ||
      execution.launched_threads != exact::word{5} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.engine_source_reads != exact::word{0} ||
      execution.logical.alternatives_retained != exact::word{1} ||
      execution.logical.reservations_consumed != exact::word{2};
  const auto& process = execution.process;
  failures += !process.returned() || process.exterior_process_calls != exact::word{1} ||
      process.host_semantic_events != exact::word{0} || !process.named_lake_env_lean ||
      !process.raw_bytes_returned || !process.environment.pinned_lean_4_27 ||
      !process.environment.pinned_mathlib_revision || process.source_bytes.value() == 0 ||
      process.produced_artifact_bytes.value() == 0;
  const auto& generation = actual.generation;
  failures += generation.obstruction != organ::theorem_production_obstruction::none ||
      generation.expansion.obstruction !=
          organ::theorem_production_obstruction::receiver_underdetermined ||
      generation.expansion.open_count != 2 || generation.expansion.retained_count != 1 ||
      generation.expansion.global_candidate_scans != 0 ||
      generation.expansion.fibers[0].dependency_count != 3 ||
      generation.expansion.fibers[1].dependency_count != 4 ||
      generation.passage.identity != exact::word{171'200} ||
      generation.passage.statement != exact::word{151'200} ||
      generation.passage.proof != exact::word{161'200} ||
      generation.passage.selected_rule != exact::word{141'010} ||
      generation.passage.formation != organ::theorem_formation::compose_then_transport ||
      !generation.passage.closed || !generation.passage.generated ||
      actual.generation_commit.state != body::body_change_status::committed ||
      actual.generation_commit.predecessor != exact::word{14'001'000} ||
      actual.generation_commit.successor != exact::word{14'001'001} ||
      actual.generation_commit.admitted_tally_before != 128 ||
      actual.generation_commit.admitted_tally_after != 135 ||
      !generation.exact_local_expansion || !generation.exact_receiver_restriction ||
      !generation.proof_current_lineaged;
  const auto& exclusion = generation.exclusion;
  failures += exclusion.mounted_answer_matches != 0 || exclusion.lookup_entries != 0 ||
      exclusion.quoted_source_bytes != 0 || exclusion.reference_calls != 0 ||
      exclusion.retained_development_source_bytes != 0 || !exclusion.target_absent_at_mount ||
      !exclusion.source_detached_at_rest;
  failures += actual.formal.passage != exact::word{171'200} ||
      actual.conversational.passage != actual.formal.passage ||
      actual.checker_face.passage != actual.formal.passage ||
      actual.checker_face.generated_source != exact::word{123'201} ||
      actual.checker_face.declaration_form !=
          codec::formal_declaration_form::composed_trace_rebase ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_trace_rebase_transports_composition") ||
      !contains(actual.formal.bytes, actual.formal.byte_count, "Trace.trans hst htu") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "trace_rebase_iff A e theta s u") ||
      actual.conversational.byte_count == 0;
  failures += actual.checker_stage != event::checker_stage_status::exact ||
      !actual.pending_before_process || actual.pending_after_return ||
      !actual.passage_preserved || actual.outbound.predecessor != exact::word{14'001'001} ||
      actual.outbound.passage != exact::word{171'200};
  failures += actual.typed.state != event::checker_return_status::accepted ||
      actual.typed.produced_declarations != 1 || actual.typed.remaining_goal_count != 0 ||
      !actual.typed.elaborator_boundary_crossed || !actual.typed.kernel_boundary_crossed ||
      actual.typed.source_span_begin >= actual.typed.source_span_end ||
      actual.raw.exit_status != 0 || actual.raw.stdout_bytes == 0 ||
      actual.raw.stderr_bytes != 0 || actual.raw.produced_artifact_bytes == 0;
  const auto& morphology = actual.returned_morphology;
  failures += morphology.mathematical_before != 43 || morphology.mathematical_after != 46 ||
      morphology.codec_before != 32 || morphology.codec_after != 34 ||
      morphology.commit.state != body::body_change_status::committed ||
      morphology.commit.predecessor != exact::word{14'001'001} ||
      morphology.commit.successor != exact::word{14'001'002} ||
      morphology.commit.admitted_tally_before != 135 || morphology.commit.admitted_tally_after != 140 ||
      !morphology.returned_difference_applied;
  failures += actual.acquired.identity != exact::word{181'200} ||
      actual.acquired.passage != exact::word{171'200} || !actual.acquired.accepted ||
      actual.acquired.admitted_tally_delta != exact::word{5} ||
      actual.before.available || actual.before.source_accesses != 0 ||
      !actual.after.available || actual.after.used_returned_fiber != exact::word{181'200} ||
      actual.after.source_accesses != 0 || !actual.behavior_changed;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      actual.rest.retained_source_bytes != 0 || !actual.remount.same_body ||
      !actual.remount.acquired_return_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.handoff_continuation_valid ||
      actual.final_head != exact::word{14'001'002};
  failures += actual.ablation.excluded_delta != exact::word{5} ||
      actual.ablation.excluded_fiber != exact::word{181'200} ||
      !actual.ablation.production.available || actual.ablation.ablated.available ||
      !actual.ablation.exact_exclusion || !actual.ablation.consequence_lost;
  failures += handoff.integrity != event::theorem_production_rest_integrity(handoff) ||
      handoff.body.head != 14'001'002 || handoff.body.regions[0].admitted_tally != 140 ||
      handoff.acquired.identity != exact::word{181'200} || !handoff.acquired.accepted ||
      handoff.mathematical_admitted_tally != 46 || handoff.codec_admitted_tally != 34;
  return failures;
}

}  // namespace holonics::tests
