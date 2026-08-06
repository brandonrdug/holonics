#include "r24_verify.hpp"

namespace holonics::tests {
namespace {

template<std::size_t Capacity, class Count, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], Count used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t width = Pattern - 1U;
  for (std::size_t start = 0; width != 0 && start + width <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < width; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return true; }
  }
  return false;
}

[[nodiscard]] std::size_t mathematical_failures(
    const organ::algebraic_variation_receipt& value) noexcept {
  std::size_t failures = !value.all_exact || !value.discriminant_exact || !value.roots_exact ||
      !value.connection.exact || !value.connection.symbolic_residual_zero ||
      !value.connection.holdouts_exact || !value.connection.pole_support_matches_discriminant ||
      !value.invariant.exact || !value.scalar.exact || !value.loops.exact ||
      !value.selection.exact || !value.alternatives_retained || !value.no_expected_names ||
      value.root_count != 3 || value.collision_count != 2 ||
      value.discriminant.coefficients[2] != 1 || value.discriminant.coefficients[3] != -2 ||
      value.discriminant.coefficients[4] != 1 || value.connection.denominator_scale != 2;
  failures += value.connection.numerator[0][0].parameter != 1 ||
      value.connection.numerator[0][1].constant != -1 ||
      value.connection.numerator[1][0].parameter != 1 ||
      value.connection.numerator[1][1].parameter != -1 ||
      value.invariant.discovery_survivors != 2 || value.invariant.selected[0][1] != 1 ||
      value.invariant.selected[1][0] != -1 || value.scalar.constraint_rank != 5;
  failures += value.scalar.second[0] != 0 || value.scalar.second[1] != 4 ||
      value.scalar.second[2] != -4 || value.scalar.first[0] != 4 ||
      value.scalar.first[1] != -8 || value.scalar.zeroth != -1 ||
      value.scalar.series[1].numerator != 1 || value.scalar.series[1].denominator != 4 ||
      value.scalar.series[2].numerator != 9 || value.scalar.series[2].denominator != 64;
  failures += value.loops.monodromy[0][0][1] != 2 ||
      value.loops.monodromy[1][1][0] != -2 ||
      value.loops.monodromy[2][0][0] != 1 || value.loops.monodromy[2][0][1] != -2 ||
      value.loops.monodromy[2][1][0] != 2 || value.loops.monodromy[2][1][1] != -3 ||
      !value.foils.squarefree_multiplicity_rejected || !value.foils.local_only_form_rejected ||
      !value.foils.euclidean_form_rejected || !value.foils.symmetric_form_rejected ||
      !value.foils.degenerate_form_rejected || !value.foils.operator_without_zeroth_rejected ||
      !value.foils.commuting_loops_rejected || !value.foils.equal_spectrum_not_equal_collision;
  return failures;
}

}  // namespace

std::size_t r24_verification_failures(
    const apparatus::variation_store_receipt& card_load,
    const apparatus::variation_store_receipt& rest_load,
    const apparatus::variation_executor_receipt& execution,
    const apparatus::variation_probe_receipt& probe,
    const organ::algebraic_variation_receipt& changed,
    const event::algebraic_variation_observation& actual,
    const event::algebraic_variation_rest_record& handoff) noexcept {
  std::size_t failures = !card_load.returned() || !rest_load.returned() ||
      !execution.returned() || !probe.returned() ||
      execution.host_semantic_events != exact::word{0} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += mathematical_failures(actual.inquiry);
  failures += changed.all_exact || changed.obstruction == organ::variation_obstruction::none ||
      changed.selection.selected.value() != 0 ||
      (changed.root_count == actual.inquiry.root_count && changed.discriminant_exact);
  const auto& passage = actual.passage;
  failures += passage.checker_stage != event::checker_stage_status::exact ||
      passage.typed.state != event::checker_return_status::accepted ||
      passage.typed.produced_declarations != 1 || passage.typed.remaining_goal_count != 0 ||
      !passage.typed.elaborator_boundary_crossed || !passage.typed.kernel_boundary_crossed ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 ||
      passage.raw.stderr_bytes != 0 || passage.raw.produced_artifact_bytes == 0 ||
      !passage.pending_before_process || passage.pending_after_return ||
      !passage.passage_preserved || !contains(passage.formal.bytes,
          passage.formal.byte_count, "theorem generated_algebraic_variation") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'020} ||
      passage.formation_commit.successor != exact::word{14'001'021} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'022} ||
      passage.returned_morphology.mathematical_after != 130 ||
      passage.returned_morphology.codec_after != 69;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      !actual.remount.same_body || !actual.remount.theory_preserved ||
      actual.remount.source_replayed || !actual.handoff.returned ||
      !actual.final_can_continue || actual.final_head != exact::word{14'001'022} ||
      actual.final_continuation != exact::word{15'001'022};
  failures += handoff.integrity != event::algebraic_variation_rest_integrity(handoff) ||
      handoff.body.regions[0].morphology != 413 || handoff.mathematical_admitted_tally != 130 ||
      handoff.codec_admitted_tally != 69 || handoff.toric_cycle_admitted_tally != 19 ||
      handoff.algebraic_variation_admitted_tally != 23 ||
      handoff.algebraic_variation.identity != exact::word{191'300} ||
      !handoff.algebraic_variation.accepted || !handoff.toric_cycle.accepted;
  return failures;
}

}  // namespace holonics::tests
