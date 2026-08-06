#include "r17_verify.hpp"

namespace holonics::tests {
namespace {

template<std::size_t Capacity, class Count, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], Count used,
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

std::size_t r17_verification_failures(
    const apparatus::geometry_store_receipt& rest_load,
    const apparatus::geometry_inquiry_executor_receipt& execution,
    const event::geometry_inquiry_observation& actual,
    const event::geometry_inquiry_rest_record& handoff,
    const apparatus::sealed_geometry_comparison& comparison) noexcept {
  std::size_t failures = 0;
  failures += !rest_load.returned() || rest_load.bytes != exact::word{264} ||
      rest_load.transfer_calls != exact::word{1} ||
      rest_load.developmental_source_bytes != exact::word{0} ||
      rest_load.retrieval_handles != exact::word{0} || !rest_load.integrity_exact;
  failures += !execution.returned() || execution.kernel_launches != exact::word{6} ||
      execution.launched_threads != exact::word{37} ||
      execution.probe_threads != exact::word{32} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.engine_source_reads != exact::word{0} ||
      execution.exterior_retrieval_calls != exact::word{0} ||
      execution.developmental_source_bytes != exact::word{0} ||
      execution.logical.alternatives_retained != exact::word{2} ||
      execution.logical.obstructions_retained != exact::word{2};
  const auto& process = execution.process;
  failures += !process.returned() || process.exterior_process_calls != exact::word{1} ||
      process.host_semantic_events != exact::word{0} || !process.named_lake_env_lean ||
      !process.raw_bytes_returned || !process.environment.pinned_lean_4_27 ||
      !process.environment.pinned_mathlib_revision || process.source_bytes.value() == 0 ||
      process.produced_artifact_bytes.value() == 0;
  failures += !actual.predecessor_remount.same_body ||
      !actual.predecessor_remount.both_returns_preserved ||
      actual.predecessor_remount.source_replayed ||
      actual.inquiry.question.identity != exact::word{143'300} ||
      actual.inquiry.returned_probe_count != 32 ||
      actual.inquiry.projective_probe_count != 31 ||
      actual.inquiry.coordinate_counterexamples != 31 ||
      actual.inquiry.singular_probe_count != 1 ||
      actual.inquiry.closed_fiber_count != 2 ||
      actual.inquiry.obstructed_fiber_count != 2 ||
      actual.inquiry.global_candidate_scans != 0 ||
      !actual.inquiry.exact_local_front || !actual.inquiry.mode_field_absent ||
      !actual.inquiry.expected_answer_absent || !actual.inquiry.theory_formed;
  for (std::size_t slot = 0; slot < 31; ++slot) {
    const auto& probe = actual.inquiry.probes[slot];
    failures += !probe.returned || !probe.projectively_equal || probe.coordinates_equal ||
        probe.quotient_singular || probe.determinant.value() == 0 ||
        probe.common_square.value() != probe.determinant.value() * probe.determinant.value() ||
        probe.transformed.first.value() !=
            probe.original.first.value() * probe.common_square.value() ||
        probe.transformed.second.value() !=
            probe.original.second.value() * probe.common_square.value();
  }
  failures += !actual.inquiry.probes[31].returned ||
      !actual.inquiry.probes[31].quotient_singular ||
      !actual.inquiry.symbolic.alpha_gamma_xy_cancelled ||
      !actual.inquiry.symbolic.beta_delta_cancelled ||
      !actual.inquiry.symbolic.determinant_factored ||
      !actual.inquiry.symbolic.complete_four_point_cancellation;
  failures += actual.inquiry.fibers[0].state != organ::geometry_fiber_state::obstructed ||
      actual.inquiry.fibers[0].obstruction !=
          organ::geometry_inquiry_obstruction::coordinate_counterexample ||
      actual.inquiry.fibers[1].state != organ::geometry_fiber_state::closed ||
      actual.inquiry.fibers[2].state != organ::geometry_fiber_state::closed ||
      actual.inquiry.fibers[3].obstruction !=
          organ::geometry_inquiry_obstruction::singular_chart;
  failures += actual.theory_commit.state != body::body_change_status::committed ||
      actual.theory_commit.predecessor != exact::word{14'001'004} ||
      actual.theory_commit.successor != exact::word{14'001'005} ||
      actual.theory_commit.admitted_tally_before != 152 ||
      actual.theory_commit.admitted_tally_after != 160;
  failures += actual.formal.passage != exact::word{173'300} ||
      actual.conversational.passage != actual.formal.passage ||
      !contains(actual.formal.bytes, actual.formal.byte_count, "theorem generated_mobius_sub") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_swing_affine_commRing") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_crossRatio_mobius") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_coordinate_counterexample") ||
      contains(actual.formal.bytes, actual.formal.byte_count,
          "ElementaryHolonics.Geometry.CrossRatio") ||
      actual.conversational.byte_count == 0;
  failures += actual.checker_stage != event::checker_stage_status::exact ||
      !actual.pending_before_process || actual.pending_after_return ||
      !actual.passage_preserved || actual.outbound.predecessor != exact::word{14'001'005} ||
      actual.outbound.event != exact::word{160'400} ||
      actual.outbound.passage != exact::word{173'300};
  failures += actual.typed.state != event::checker_return_status::accepted ||
      actual.typed.produced_declarations != 1 || actual.typed.remaining_goal_count != 0 ||
      !actual.typed.elaborator_boundary_crossed || !actual.typed.kernel_boundary_crossed ||
      actual.raw.exit_status != 0 || actual.raw.stdout_bytes == 0 ||
      actual.raw.stderr_bytes != 0 || actual.raw.produced_artifact_bytes == 0;
  const auto& morphology = actual.returned_morphology;
  failures += morphology.mathematical_before != 49 || morphology.mathematical_after != 55 ||
      morphology.codec_before != 36 || morphology.codec_after != 39 ||
      morphology.commit.state != body::body_change_status::committed ||
      morphology.commit.predecessor != exact::word{14'001'005} ||
      morphology.commit.successor != exact::word{14'001'006} ||
      morphology.commit.admitted_tally_before != 160 ||
      morphology.commit.admitted_tally_after != 169 ||
      !morphology.returned_difference_applied;
  failures += actual.acquired.identity != exact::word{184'300} ||
      actual.acquired.passage != exact::word{173'300} ||
      actual.acquired.kernel_return != exact::word{160'400} ||
      actual.acquired.admitted_tally_delta != exact::word{9} || !actual.acquired.accepted;
  failures += !actual.rest.returned || !actual.rest.prior_theorems_preserved ||
      !actual.rest.source_detached || !actual.remount.same_body ||
      !actual.remount.theory_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.final_can_continue ||
      actual.final_head != exact::word{14'001'006} ||
      actual.final_continuation != exact::word{15'001'006};
  failures += handoff.integrity != event::geometry_inquiry_rest_integrity(handoff) ||
      handoff.body.head != 14'001'006 || handoff.body.continuation != 15'001'006 ||
      handoff.body.regions[0].admitted_tally != 169 ||
      handoff.first.identity != exact::word{181'200} || !handoff.first.accepted ||
      handoff.second.identity != exact::word{182'200} || !handoff.second.accepted ||
      handoff.geometry.identity != exact::word{184'300} || !handoff.geometry.accepted ||
      handoff.mathematical_admitted_tally != 55 || handoff.codec_admitted_tally != 39 ||
      handoff.geometry_admitted_tally != 10;
  failures += !comparison.returned() || !comparison.opened_after_kernel_return ||
      !comparison.affine_neighbor_present || comparison.fractional_neighbor_present ||
      comparison.body_resumed_after_open || comparison.observer_reads != exact::word{1} ||
      comparison.engine_reads != exact::word{0} || comparison.bytes.value() == 0;
  return failures;
}

}  // namespace holonics::tests
