#include "r19_verify.hpp"

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

std::size_t r19_verification_failures(
    const apparatus::characteristic_store_receipt& rest_load,
    const apparatus::characteristic_executor_receipt& execution,
    const event::characteristic_observation& actual,
    const event::characteristic_rest_record& handoff) noexcept {
  std::size_t failures = 0;
  failures += !rest_load.returned() || rest_load.transfer_calls != exact::word{1} ||
      rest_load.source_bytes != exact::word{0} || rest_load.retrieval_handles != exact::word{0} ||
      !rest_load.integrity_exact;
  failures += !execution.returned() || execution.kernel_launches != exact::word{6} ||
      execution.launched_threads != exact::word{21} ||
      execution.case_threads != exact::word{16} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.engine_source_reads != exact::word{0} ||
      execution.exterior_retrieval_calls != exact::word{0} ||
      execution.historical_renderer_bytes != exact::word{0} ||
      execution.logical.obstructions_retained != exact::word{0};
  const auto& process = execution.process;
  failures += !process.returned() || process.exterior_process_calls != exact::word{1} ||
      process.host_semantic_events != exact::word{0} || !process.named_lake_env_lean ||
      !process.raw_bytes_returned || !process.environment.pinned_lean_4_27 ||
      !process.environment.pinned_mathlib_revision || process.source_bytes.value() == 0 ||
      process.produced_artifact_bytes.value() == 0;
  const auto& inquiry = actual.inquiry;
  failures += !actual.predecessor_remount.same_body ||
      !actual.predecessor_remount.atlas_preserved ||
      actual.predecessor_remount.source_replayed ||
      inquiry.question.identity != exact::word{144'400} || inquiry.returned_cases != 16 ||
      inquiry.repeated_mode_cases != 2 || inquiry.simple_mode_cases != 14 ||
      inquiry.shape_tour_classes == 0 || !inquiry.no_expected_eigenvalue ||
      !inquiry.no_prime_mode_label || !inquiry.no_renderer_source ||
      !inquiry.all_cases_exact || !inquiry.scalar.exact || !inquiry.matrices.exact ||
      !inquiry.indicial.exact || !inquiry.theory_formed ||
      inquiry.obstruction != organ::characteristic_obstruction::none;
  std::uint32_t degrees = 0;
  for (std::size_t slot = 0; slot < organ::characteristic_case_capacity; ++slot) {
    const auto& value = inquiry.cases[slot];
    degrees += value.characteristic_degree;
    failures += !value.exact || value.gcd * value.lcm != value.vertices ||
        value.tours != value.gcd || value.tour_length != value.lcm ||
        value.characteristic_degree != value.vertices ||
        value.minimal_degree != value.lcm || value.mode_multiplicity != value.gcd ||
        value.shape_types == 0 || value.shape_tour_classes == 0 ||
        value.shape_exponent_total != value.vertices || !value.orbit_exact ||
        !value.characteristic_factor_exact || !value.minimal_factor_exact ||
        !value.cycle_factor_squarefree || value.local_transport_singular ||
        !value.formal_shape_transport_exact;
    failures += value.global_discriminant_zero != (value.gcd > 1);
  }
  failures += degrees != 1'460 || inquiry.cases[9].mode_multiplicity != 3 ||
      inquiry.cases[10].mode_multiplicity != 4;
  failures += inquiry.scalar.first_product != 30 || inquiry.scalar.second_product != 30 ||
      !inquiry.scalar.characteristic_equal || !inquiry.scalar.lineage_distinct;
  const auto& matrices = inquiry.matrices;
  failures += matrices.first_trace != 5 || matrices.second_trace != 4 ||
      matrices.first_determinant != 2 || matrices.second_determinant != 2 ||
      !matrices.order_changes_characteristic || !matrices.order_lineage_distinct ||
      matrices.first_lineage == matrices.second_lineage ||
      !matrices.rechart_preserves_characteristic ||
      matrices.rechart_lineage == 0 ||
      matrices.rechart_trace != 3 || matrices.rechart_determinant != 1 ||
      matrices.independent_fixed_dimension != 2 || matrices.coupled_fixed_dimension != 1 ||
      !matrices.equal_characteristic_unequal_conduct;
  failures += !inquiry.indicial.zero_roots_zero_negative_one ||
      !inquiry.indicial.one_repeated_zero || !inquiry.indicial.infinity_repeated_one ||
      !inquiry.indicial.recurrence_is_only_one_local_branch;
  failures += actual.formation_commit.state != body::body_change_status::committed ||
      actual.formation_commit.predecessor != exact::word{14'001'008} ||
      actual.formation_commit.successor != exact::word{14'001'009} ||
      actual.formation_commit.morphology_before != 192 ||
      actual.formation_commit.morphology_after != 205;
  failures += actual.formal.passage != exact::word{174'400} ||
      actual.conversational.passage != actual.formal.passage ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_diagonal_characteristic_degree") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_weighted_two_cycle") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_rechart_characteristic") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_gauss_indicial") || actual.conversational.byte_count == 0;
  failures += actual.checker_stage != event::checker_stage_status::exact ||
      !actual.pending_before_process || actual.pending_after_return ||
      !actual.passage_preserved || actual.outbound.predecessor != exact::word{14'001'009} ||
      actual.outbound.event != exact::word{160'600} ||
      actual.outbound.passage != exact::word{174'400};
  failures += actual.typed.state != event::checker_return_status::accepted ||
      actual.typed.produced_declarations != 1 || actual.typed.remaining_goal_count != 0 ||
      !actual.typed.elaborator_boundary_crossed || !actual.typed.kernel_boundary_crossed ||
      actual.raw.exit_status != 0 || actual.raw.stdout_bytes == 0 ||
      actual.raw.stderr_bytes != 0 || actual.raw.produced_artifact_bytes == 0;
  const auto& morphology = actual.returned_morphology;
  failures += morphology.mathematical_before != 62 || morphology.mathematical_after != 70 ||
      morphology.codec_before != 42 || morphology.codec_after != 45 ||
      morphology.commit.state != body::body_change_status::committed ||
      morphology.commit.predecessor != exact::word{14'001'009} ||
      morphology.commit.successor != exact::word{14'001'010} ||
      morphology.commit.morphology_before != 205 ||
      morphology.commit.morphology_after != 217 || !morphology.returned_difference_applied;
  failures += actual.acquired.identity != exact::word{186'300} ||
      actual.acquired.passage != exact::word{174'400} ||
      actual.acquired.kernel_return != exact::word{160'600} ||
      actual.acquired.morphology_delta != exact::word{12} || !actual.acquired.accepted;
  failures += !actual.rest.returned || !actual.rest.prior_returns_preserved ||
      !actual.rest.source_detached || !actual.remount.same_body ||
      !actual.remount.theory_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.final_can_continue ||
      actual.final_head != exact::word{14'001'010} ||
      actual.final_continuation != exact::word{15'001'010};
  failures += handoff.integrity != event::characteristic_rest_integrity(handoff) ||
      handoff.body.head != 14'001'010 || handoff.body.continuation != 15'001'010 ||
      handoff.body.regions[0].morphology != 217 ||
      handoff.first.identity != exact::word{181'200} || !handoff.first.accepted ||
      handoff.second.identity != exact::word{182'200} || !handoff.second.accepted ||
      handoff.geometry.identity != exact::word{184'300} || !handoff.geometry.accepted ||
      handoff.phase_crystal.identity != exact::word{185'300} ||
      !handoff.phase_crystal.accepted ||
      handoff.characteristic.identity != exact::word{186'300} ||
      !handoff.characteristic.accepted || handoff.mathematical_morphology != 70 ||
      handoff.codec_morphology != 45 || handoff.geometry_morphology != 10 ||
      handoff.phase_morphology != 14 || handoff.characteristic_morphology != 16;
  return failures;
}

}  // namespace holonics::tests
