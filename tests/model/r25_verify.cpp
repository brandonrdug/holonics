#include "r25_verify.hpp"

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
    const organ::causal_linear_receipt& value) noexcept {
  std::size_t failures = !value.all_exact || !value.theory_formed ||
      value.source_mask != 15 || !value.source_sections_independent ||
      !value.alternatives_retained || !value.no_expected_invariants ||
      value.obstruction != organ::causal_linear_obstruction::none;
  failures += !value.phase.exact || value.phase.vertices != 6 || value.phase.edges != 12 ||
      value.phase.faces != 6 || value.phase.boundary_one_analysis.rank != 5 ||
      value.phase.boundary_two_analysis.rank != 5 || !value.phase.boundary_composite_zero ||
      value.phase.betti[0] != 1 || value.phase.betti[1] != 2 ||
      value.phase.betti[2] != 1 || value.phase.tours != 1 || value.phase.tour_length != 6;
  failures += !value.cm.exact || value.cm.vertices != 16 || value.cm.edges != 40 ||
      value.cm.incidence_analysis.rank != 15 || value.cm.homology_zero != 1 ||
      value.cm.homology_one != 25 || !value.cm.domain_characteristic_agrees ||
      !value.cm.factor_exact || value.cm.factor_count != 3;
  failures += !value.toric.exact || value.toric.source[0].free_cokernel_rank != 1 ||
      value.toric.source[1].free_cokernel_rank != 2 ||
      value.toric.blowup.free_cokernel_rank != 2 || value.toric.exceptional_square != -1 ||
      !value.toric.topology_changed;
  for (std::uint8_t map = 0; map < 2; ++map) {
    failures += value.toric.source[map].smith[0] != 1 ||
        value.toric.source[map].smith[1] != 1;
  }
  failures += value.toric.blowup.smith[0] != 1 || value.toric.blowup.smith[1] != 1;
  failures += !value.variation.exact || value.variation.determinant[0] != 0 ||
      value.variation.determinant[1] != 1 || value.variation.determinant[2] != -1 ||
      value.variation.ranks[0] != 1 || value.variation.ranks[1] != 1 ||
      value.variation.ranks[2] != 2 || !value.variation.adjoints_exact ||
      !value.variation.exterior_exact || !value.variation.tensor_characteristic.exact;
  failures += !value.controls.exact || !value.controls.equal_characteristic_unequal_fixed ||
      value.controls.identity_fixed != 2 || value.controls.jordan_fixed != 1 ||
      !value.controls.unequal_kernel_placement || !value.controls.conjugacy_exact ||
      value.controls.rational_discriminant != -4 ||
      !value.controls.rational_eigenvalue_absent || !value.controls.gaussian_eigenpair_exact;
  return failures;
}

}  // namespace

std::size_t r25_verification_failures(bool sources_loaded,
    const apparatus::causal_linear_store_receipt& rest_load,
    const apparatus::causal_linear_executor_receipt& execution,
    const apparatus::causal_linear_probe_receipt& probe,
    const organ::causal_linear_receipt& changed,
    const event::causal_linear_observation& actual,
    const event::causal_linear_rest_record& handoff) noexcept {
  std::size_t failures = !sources_loaded || !rest_load.returned() ||
      !execution.returned() || !probe.returned() ||
      execution.host_semantic_events != exact::word{0} ||
      execution.semantic_threads != exact::word{8} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += mathematical_failures(actual.inquiry);
  failures += !changed.all_exact || !changed.phase.exact || changed.phase.vertices != 8 ||
      changed.phase.edges != 16 || changed.phase.faces != 8 ||
      changed.phase.boundary_one_analysis.rank != 7 ||
      changed.phase.boundary_two_analysis.rank != 7 ||
      changed.phase.betti[0] != 1 || changed.phase.betti[1] != 2 ||
      changed.phase.betti[2] != 1 || changed.phase.tours != 2 ||
      changed.phase.tour_length != 4 || !changed.cm.exact || !changed.toric.exact ||
      !changed.variation.exact || !changed.controls.exact;
  const auto& passage = actual.passage;
  failures += passage.checker_stage != event::checker_stage_status::exact ||
      passage.typed.state != event::checker_return_status::accepted ||
      passage.typed.produced_declarations != 1 || passage.typed.remaining_goal_count != 0 ||
      !passage.typed.elaborator_boundary_crossed || !passage.typed.kernel_boundary_crossed ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 ||
      passage.raw.stderr_bytes != 0 || passage.raw.produced_artifact_bytes == 0 ||
      !passage.pending_before_process || passage.pending_after_return ||
      !passage.passage_preserved || !contains(passage.formal.bytes,
          passage.formal.byte_count, "theorem generated_causal_linear_calculus") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'022} ||
      passage.formation_commit.successor != exact::word{14'001'023} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'024} ||
      passage.returned_morphology.mathematical_after != 146 ||
      passage.returned_morphology.codec_after != 76;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      !actual.remount.same_body || !actual.remount.theory_preserved ||
      actual.remount.source_replayed || !actual.handoff.returned ||
      !actual.final_can_continue || actual.final_head != exact::word{14'001'024} ||
      actual.final_continuation != exact::word{15'001'024};
  failures += handoff.integrity != event::causal_linear_rest_integrity(handoff) ||
      handoff.body.regions[0].morphology != 472 || handoff.mathematical_morphology != 146 ||
      handoff.codec_morphology != 76 || handoff.algebraic_variation_morphology != 23 ||
      handoff.causal_linear_morphology != 29 ||
      handoff.causal_linear.identity != exact::word{192'300} ||
      !handoff.causal_linear.accepted || !handoff.algebraic_variation.accepted;
  return failures;
}

}  // namespace holonics::tests
