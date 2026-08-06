#include "r20_verify.hpp"

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

[[nodiscard]] bool matrix_is(organ::matrix_two value,
    std::int64_t a, std::int64_t b, std::int64_t c, std::int64_t d) noexcept {
  return value.a == a && value.b == b && value.c == c && value.d == d;
}

}  // namespace

std::size_t r20_verification_failures(
    const apparatus::regular_singular_store_receipt& rest_load,
    const apparatus::regular_singular_executor_receipt& execution,
    const event::regular_singular_observation& actual,
    const event::regular_singular_rest_record& handoff) noexcept {
  std::size_t failures = 0;
  failures += !rest_load.returned() || rest_load.transfer_calls != exact::word{1} ||
      rest_load.source_bytes != exact::word{0} || rest_load.retrieval_handles != exact::word{0} ||
      !rest_load.integrity_exact;
  failures += !execution.returned() || execution.kernel_launches != exact::word{7} ||
      execution.launched_threads != exact::word{20} ||
      execution.chart_threads != exact::word{3} ||
      execution.coefficient_threads != exact::word{12} ||
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
      !actual.predecessor_remount.theory_preserved ||
      actual.predecessor_remount.source_replayed ||
      inquiry.question.identity != exact::word{145'400} ||
      inquiry.returned_charts != 3 || inquiry.returned_terms != 12 ||
      inquiry.logarithmic_charts != 2 || !inquiry.no_special_function_lookup ||
      !inquiry.no_numerical_continuation || !inquiry.no_expected_logarithm ||
      !inquiry.no_expected_eigenvector || !inquiry.system.derived ||
      !inquiry.all_exact || !inquiry.connection.exact || !inquiry.theory_formed ||
      inquiry.obstruction != organ::regular_singular_obstruction::none;
  failures += !matrix_is(inquiry.system.zero, 0, 1, 0, -1) ||
      !matrix_is(inquiry.system.one, 0, 0, -1, -1) ||
      !matrix_is(inquiry.system.infinity, 0, -1, 1, 2);
  const auto& zero = inquiry.charts[0];
  const auto& one = inquiry.charts[1];
  const auto& infinity = inquiry.charts[2];
  failures += !zero.exact || zero.trace != -1 || zero.determinant != 0 ||
      zero.characteristic_discriminant != 1 || zero.eigenvalue_gap != 1 ||
      zero.resonant_source[0] != 0 || zero.resonant_source[1] != 0 ||
      zero.obstruction_scalar != 0 || zero.logarithmic_channel;
  failures += !one.exact || one.trace != -1 || one.determinant != 0 ||
      one.characteristic_discriminant != 1 || one.eigenvalue_gap != 1 ||
      one.resonant_source[0] != 1 || one.resonant_source[1] != -1 ||
      one.recurrence_cokernel[0] != 1 || one.recurrence_cokernel[1] != 0 ||
      one.obstruction_scalar != 1 || !one.logarithmic_channel;
  failures += !infinity.exact || infinity.trace != 2 || infinity.determinant != 1 ||
      infinity.characteristic_discriminant != 0 || infinity.lower_eigenvalue != 1 ||
      infinity.upper_eigenvalue != 1 || infinity.nilpotent_rank != 1 ||
      infinity.eigenflag_dimension != 1 || !infinity.logarithmic_channel;
  for (std::size_t slot = 0; slot < organ::regular_singular_term_capacity; ++slot) {
    const auto& term = inquiry.terms[slot];
    failures += !term.exact || term.degree != slot || term.zero_numerator != 1 ||
        term.zero_denominator != static_cast<std::int64_t>(slot + 1U) ||
        term.one_regular != 1 || term.one_logarithmic != -1 ||
        term.zero_step_lhs != term.zero_step_rhs || term.one_step_residual != 0 ||
        term.lineage == 0;
  }
  const auto& connection = inquiry.connection;
  failures += !matrix_is(connection.zero_to_one, 0, 1, 1, 0) ||
      !matrix_is(connection.one_to_zero, 0, 1, 1, 0) ||
      connection.connection_determinant != -1 || !connection.inverse_exact ||
      !connection.conjugacy_exact || !connection.punctured_sphere_product_exact ||
      !connection.period_symbolic || connection.zero_fixed_dimension != 2 ||
      connection.one_fixed_dimension != 1 || connection.infinity_fixed_dimension != 1 ||
      connection.one_nilpotent_rank != 1 || connection.infinity_nilpotent_rank != 1 ||
      connection.connection_lineage == 0 || connection.loop_lineages[0] == 0 ||
      connection.loop_lineages[1] == 0 || connection.loop_lineages[2] == 0 ||
      connection.loop_lineages[0] == connection.loop_lineages[1] ||
      connection.loop_lineages[1] == connection.loop_lineages[2] ||
      connection.loop_lineage == 0;
  failures += connection.monodromy_one.b.constant != 0 ||
      connection.monodromy_one.b.omega != -1 ||
      connection.monodromy_infinity.b.omega != 1 ||
      connection.loop_product.a.constant != 1 ||
      connection.loop_product.b.constant != 0 ||
      connection.loop_product.b.omega != 0 ||
      connection.loop_product.d.constant != 1 ||
      connection.one_loop_in_zero_basis.c.omega != -1;
  failures += actual.formation_commit.state != body::body_change_status::committed ||
      actual.formation_commit.predecessor != exact::word{14'001'010} ||
      actual.formation_commit.successor != exact::word{14'001'011} ||
      actual.formation_commit.admitted_tally_before != 217 ||
      actual.formation_commit.admitted_tally_after != 231;
  failures += actual.formal.passage != exact::word{175'400} ||
      actual.conversational.passage != actual.formal.passage ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_residue_algebra") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_zero_frobenius_step") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_resonance_obstruction") ||
      !contains(actual.formal.bytes, actual.formal.byte_count,
          "theorem generated_connection_and_loop") ||
      actual.conversational.byte_count == 0;
  failures += actual.checker_stage != event::checker_stage_status::exact ||
      !actual.pending_before_process || actual.pending_after_return ||
      !actual.passage_preserved || actual.outbound.predecessor != exact::word{14'001'011} ||
      actual.outbound.event != exact::word{160'700} ||
      actual.outbound.passage != exact::word{175'400};
  failures += actual.typed.state != event::checker_return_status::accepted ||
      actual.typed.produced_declarations != 1 || actual.typed.remaining_goal_count != 0 ||
      !actual.typed.elaborator_boundary_crossed || !actual.typed.kernel_boundary_crossed ||
      actual.raw.exit_status != 0 || actual.raw.stdout_bytes == 0 ||
      actual.raw.stderr_bytes != 0 || actual.raw.produced_artifact_bytes == 0;
  const auto& morphology = actual.returned_morphology;
  failures += morphology.mathematical_before != 70 || morphology.mathematical_after != 79 ||
      morphology.codec_before != 45 || morphology.codec_after != 48 ||
      morphology.commit.state != body::body_change_status::committed ||
      morphology.commit.predecessor != exact::word{14'001'011} ||
      morphology.commit.successor != exact::word{14'001'012} ||
      morphology.commit.admitted_tally_before != 231 ||
      morphology.commit.admitted_tally_after != 244 ||
      !morphology.returned_difference_applied;
  failures += actual.acquired.identity != exact::word{187'300} ||
      actual.acquired.passage != exact::word{175'400} ||
      actual.acquired.kernel_return != exact::word{160'700} ||
      actual.acquired.admitted_tally_delta != exact::word{13} || !actual.acquired.accepted;
  failures += !actual.rest.returned || !actual.rest.prior_returns_preserved ||
      !actual.rest.source_detached || !actual.remount.same_body ||
      !actual.remount.theory_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.final_can_continue ||
      actual.final_head != exact::word{14'001'012} ||
      actual.final_continuation != exact::word{15'001'012};
  failures += handoff.integrity != event::regular_singular_rest_integrity(handoff) ||
      handoff.body.head != 14'001'012 || handoff.body.continuation != 15'001'012 ||
      handoff.body.regions[0].admitted_tally != 244 ||
      handoff.first.identity != exact::word{181'200} || !handoff.first.accepted ||
      handoff.second.identity != exact::word{182'200} || !handoff.second.accepted ||
      handoff.geometry.identity != exact::word{184'300} || !handoff.geometry.accepted ||
      handoff.phase_crystal.identity != exact::word{185'300} ||
      !handoff.phase_crystal.accepted ||
      handoff.characteristic.identity != exact::word{186'300} ||
      !handoff.characteristic.accepted ||
      handoff.regular_singular.identity != exact::word{187'300} ||
      !handoff.regular_singular.accepted || handoff.mathematical_admitted_tally != 79 ||
      handoff.codec_admitted_tally != 48 || handoff.geometry_admitted_tally != 10 ||
      handoff.phase_admitted_tally != 14 || handoff.characteristic_admitted_tally != 16 ||
      handoff.regular_singular_admitted_tally != 20;
  return failures;
}

}  // namespace holonics::tests
