#include "r18_verify.hpp"

namespace holonics::tests {
namespace {
template<std::size_t Capacity, class Count, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], Count used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) { same = same && bytes[start + slot] == pattern[slot]; }
    if (same) { return true; }
  }
  return false;
}

}  // namespace

std::size_t r18_verification_failures(
    const apparatus::phase_crystal_store_receipt& rest_load,
    const apparatus::phase_crystal_executor_receipt& execution,
    const event::phase_crystal_observation& actual,
    const event::phase_crystal_rest_record& handoff) noexcept {
  std::size_t failures = 0;
  failures += !rest_load.returned() || rest_load.transfer_calls != exact::word{1} ||
      rest_load.source_bytes != exact::word{0} || rest_load.retrieval_handles != exact::word{0} ||
      !rest_load.integrity_exact;
  failures += !execution.returned() || execution.kernel_launches != exact::word{6} ||
      execution.launched_threads != exact::word{21} || execution.case_threads != exact::word{16} ||
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
      !actual.predecessor_remount.theory_preserved || actual.predecessor_remount.source_replayed ||
      inquiry.question.identity != exact::word{144'300} || inquiry.returned_cases != 16 ||
      inquiry.prime_cases != 7 || inquiry.composite_cases != 5 ||
      inquiry.shared_factor_cases != 2 || inquiry.control_cases != 9 ||
      inquiry.total_shape_types == 0 || inquiry.total_transition_types == 0 ||
      !inquiry.all_intrinsic_cells_exact || !inquiry.all_series_exact ||
      !inquiry.dilation_control_exact || !inquiry.turn_control_exact ||
      !inquiry.reversal_control_exact || !inquiry.mode_field_absent ||
      !inquiry.expected_shape_absent || !inquiry.historical_renderer_absent ||
      !inquiry.theory_formed || inquiry.obstruction != organ::phase_crystal_obstruction::none;
  for (std::size_t slot = 0; slot < organ::phase_crystal_case_capacity; ++slot) {
    const auto& value = inquiry.cases[slot];
    failures += !value.exact || value.gcd * value.lcm != value.vertex_count ||
        value.orbit_count != value.gcd || value.orbit_length != value.lcm ||
        value.phase_edge_count != 2U * value.vertex_count ||
        value.cell_count != value.vertex_count || value.seam_count != value.phase_edge_count ||
        value.cell_shape_types != value.first_edge_types * value.second_edge_types ||
        value.shape_transition_types == 0 || value.hull_corners < 3 ||
        value.contracted_sides == 0 || value.hull_edge_types == 0 ||
        value.boundary_residual != 0 || !value.orbit_partition_exact ||
        !value.complete_boundary_cancels || !value.cell_population_factorized ||
        !value.chronology_distribution_exact || !value.hull_exact ||
        !value.series_recurrence_exact || !value.series_closed_form_detected ||
        !value.carrier_coordinate_dimension_four || !value.cell_dimension_two ||
        !value.receiver_dimension_two ||
        value.screen_crossings_are_contacts;
  }
  failures += inquiry.cases[9].gcd != 3 || inquiry.cases[9].lcm != 18 ||
      inquiry.cases[10].gcd != 4 || inquiry.cases[10].lcm != 24 ||
      !inquiry.cases[3].coprime || inquiry.cases[9].coprime;
  failures += !inquiry.theory.diagonal_lcm || !inquiry.theory.coprime_full_tour ||
      !inquiry.theory.cell_population_product || !inquiry.theory.seam_cancellation ||
      !inquiry.theory.gauss_transport || !inquiry.theory.projection_distinguished;
  failures += actual.formation_commit.state != body::body_change_status::committed ||
      actual.formation_commit.predecessor != exact::word{14'001'006} ||
      actual.formation_commit.successor != exact::word{14'001'007} ;
  failures += actual.formal.passage != exact::word{174'300} ||
      actual.conversational.passage != actual.formal.passage ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_diagonal_return") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_coprime_diagonal_return") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_cell_population_product") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_gauss_112_transport") || actual.conversational.byte_count == 0;
  failures += actual.checker_stage != event::checker_stage_status::exact ||
      !actual.pending_before_process || actual.pending_after_return || !actual.passage_preserved ||
      actual.outbound.predecessor != exact::word{14'001'007} ||
      actual.outbound.event != exact::word{160'500} ||
      actual.outbound.passage != exact::word{174'300};
  failures += actual.typed.state != event::checker_return_status::accepted ||
      actual.typed.produced_declarations != 1 || actual.typed.remaining_goal_count != 0 ||
      !actual.typed.elaborator_boundary_crossed || !actual.typed.kernel_boundary_crossed ||
      actual.raw.exit_status != 0 || actual.raw.stdout_bytes == 0 ||
      actual.raw.stderr_bytes != 0 || actual.raw.produced_artifact_bytes == 0;
  const auto& morphology = actual.returned_morphology;
  failures +=
      morphology.commit.state != body::body_change_status::committed ||
      morphology.commit.predecessor != exact::word{14'001'007} ||
      morphology.commit.successor != exact::word{14'001'008} ||
      !morphology.returned_difference_applied;
  failures += actual.acquired.identity != exact::word{185'300} ||
      actual.acquired.passage != exact::word{174'300} ||
      actual.acquired.kernel_return != exact::word{160'500} || !actual.acquired.accepted;
  failures += !actual.rest.returned || !actual.rest.prior_returns_preserved ||
      !actual.rest.source_detached || !actual.remount.same_body ||
      !actual.remount.atlas_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.final_can_continue ||
      actual.final_head != exact::word{14'001'008} ||
      actual.final_continuation != exact::word{15'001'008};
  failures += handoff.integrity != event::phase_crystal_rest_integrity(handoff) ||
      handoff.body.head != 14'001'008 || handoff.body.continuation != 15'001'008 ||
      handoff.first.identity != exact::word{181'200} || !handoff.first.accepted ||
      handoff.second.identity != exact::word{182'200} || !handoff.second.accepted ||
      handoff.geometry.identity != exact::word{184'300} || !handoff.geometry.accepted ||
      handoff.phase_crystal.identity != exact::word{185'300} || !handoff.phase_crystal.accepted ;
  return failures;
}

}  // namespace holonics::tests
