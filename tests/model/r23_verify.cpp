#include "r23_verify.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] bool rational(exact::small_rational value,
    std::int64_t numerator, std::int64_t denominator = 1) noexcept {
  return value.numerator == numerator && value.denominator == denominator;
}

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

[[nodiscard]] std::size_t fan_failures(const organ::toric_cycle_receipt& value) noexcept {
  std::size_t failures = 0;
  for (std::uint8_t fan = 0; fan < 2; ++fan) {
    failures += !value.fans[fan].primitive || !value.fans[fan].smooth ||
        !value.fans[fan].complete || !value.fans[fan].character_exact ||
        !value.quotients[fan].smith_exact || !value.quotients[fan].torsion_free ||
        !value.quotients[fan].exact || !value.intersections[fan].fan_chow_agree ||
        !value.intersections[fan].inertia_exact || !value.intersections[fan].exact ||
        !value.comparisons[fan].standard_hypotheses ||
        !value.comparisons[fan].ranks_returned ||
        value.comparisons[fan].betti[0] != 1 ||
        value.comparisons[fan].betti[2] != value.quotients[fan].rank ||
        value.comparisons[fan].betti[4] != 1 ||
        value.comparisons[fan].hodge[1][1] != value.quotients[fan].rank ||
        value.fans[fan].smith_invariants[0] != 1 ||
        value.fans[fan].smith_invariants[1] != 1;
    for (std::uint8_t cone = 0; cone < value.fans[fan].cone_count; ++cone) {
      failures += value.fans[fan].cone_determinants[cone] != 1;
    }
  }
  failures += value.quotients[0].rank != 1 || value.quotients[1].rank != 2 ||
      value.intersections[0].rank != 1 || value.intersections[1].rank != 2 ||
      !rational(value.intersections[0].determinant, 1) ||
      !rational(value.intersections[1].determinant, -1) ||
      value.intersections[0].positive != 1 || value.intersections[0].negative != 0 ||
      value.intersections[1].positive != 1 || value.intersections[1].negative != 1 ||
      !rational(value.intersections[0].quotient_form[0][0], 1) ||
      !rational(value.intersections[1].quotient_form[0][0], 0) ||
      !rational(value.intersections[1].quotient_form[0][1], 1) ||
      !rational(value.intersections[1].quotient_form[1][0], 1) ||
      !rational(value.intersections[1].quotient_form[1][1], 0) ||
      !rational(value.intersections[1].congruence_form[0][0], 2) ||
      !rational(value.intersections[1].congruence_form[0][1], 0) ||
      !rational(value.intersections[1].congruence_form[1][1], -2) ||
      !rational(value.intersections[1].basis_determinant, -2);
  return failures;
}

[[nodiscard]] std::size_t realization_failures(
    const organ::toric_cycle_receipt& value) noexcept {
  std::size_t failures = value.realizations[0].state !=
          organ::toric_realization_state::integral ||
      value.realizations[1].state != organ::toric_realization_state::rational_only ||
      value.realizations[2].state != organ::toric_realization_state::incompatible ||
      !value.realizations[0].exact || !value.realizations[1].exact ||
      !value.realizations[2].exact || !value.realizations[0].full_response_checked ||
      !value.realizations[1].full_response_checked ||
      value.realizations[2].full_response_checked ||
      value.realizations[0].representative_count == 0 ||
      value.realizations[1].representative_count == 0 ||
      value.realizations[0].kernel_rank != 2 || value.realizations[1].kernel_rank != 2 ||
      value.realizations[2].kernel_rank != 2;
  failures += !rational(value.realizations[0].class_coordinates[0], 2) ||
      !rational(value.realizations[0].class_coordinates[1], 3) ||
      !rational(value.realizations[1].class_coordinates[0], 1, 2) ||
      !rational(value.realizations[1].class_coordinates[1], 0);
  failures += !value.polarization.response_positive || !value.polarization.negative_control ||
      !value.source_polarization.exact || !value.source_polarization.response_positive ||
      value.source_polarization.has_orthogonal_direction ||
      !rational(value.source_polarization.primitive[0], 1) ||
      !rational(value.polarization.primitive[0], 1) ||
      !rational(value.polarization.primitive[1], 1) ||
      !rational(value.polarization.primitive_negative[0], 1) ||
      !rational(value.polarization.primitive_negative[1], -1) ||
      !rational(value.polarization.primitive_square, -2);
  for (std::uint8_t target = 0; target < 2; ++target) {
    for (std::uint16_t slot = 0; slot < value.realizations[target].representative_count;
        ++slot) {
      failures += value.realizations[target].representatives[slot].identity.value() == 0 ||
          value.realizations[target].representatives[slot].lineage == 0;
    }
  }
  for (std::uint8_t ray = 0; ray < 4; ++ray) {
    failures += value.realizations[0].principal_kernel[0][ray] !=
        value.quotients[1].principal_relations[0][ray];
  }
  return failures;
}

[[nodiscard]] std::size_t blowup_failures(
    const organ::toric_cycle_receipt& value) noexcept {
  const auto& blowup = value.blowup;
  std::size_t failures = !blowup.exact || !blowup.projection_formula ||
      blowup.derived_ray.x != 1 || blowup.derived_ray.y != 1 ||
      blowup.fan.source.ray_count != 4 || blowup.quotient.rank != 2 ||
      blowup.intersection.positive != 1 || blowup.intersection.negative != 1 ||
      !rational(blowup.intersection.quotient_form[0][0], 0) ||
      !rational(blowup.intersection.quotient_form[0][1], 1) ||
      !rational(blowup.intersection.quotient_form[1][1], 1) ||
      !rational(blowup.intersection.determinant, -1) ||
      !rational(blowup.intersection.congruence_form[0][0], 1) ||
      !rational(blowup.intersection.congruence_form[0][1], 0) ||
      !rational(blowup.intersection.congruence_form[1][1], -1) ||
      !rational(blowup.intersection.basis_determinant, -1) ||
      !rational(blowup.exceptional[0], -1) ||
      !rational(blowup.exceptional[1], 1) ||
      !rational(blowup.exceptional_square, -1) ||
      !rational(blowup.pullback[0], 0) || !rational(blowup.pullback[1], 1) ||
      !rational(blowup.pushforward[0], 1) || !rational(blowup.pushforward[1], 1) ||
      !rational(blowup.transforms[0].strict[0], 1) ||
      !rational(blowup.transforms[0].strict[1], 0) ||
      !rational(blowup.transforms[0].total[0], 0) ||
      !rational(blowup.transforms[0].total[1], 1) ||
      !rational(blowup.transforms[1].strict[0], 1) ||
      !rational(blowup.transforms[1].strict[1], 0) ||
      !rational(blowup.transforms[1].total[0], 0) ||
      !rational(blowup.transforms[1].total[1], 1) ||
      !rational(blowup.transforms[2].total[0], 0) ||
      !rational(blowup.transforms[2].total[1], 1) ||
      !blowup.transforms[0].exact || !blowup.transforms[1].exact ||
      !blowup.transforms[2].exact || blowup.transforms[0].identity.value() == 0 ||
      blowup.transforms[0].lineage == 0 ||
      blowup.pullback_kernel_rank != 0 || blowup.pullback_image_rank != 1 ||
      blowup.pushforward_kernel_rank != 1 || blowup.pushforward_image_rank != 1 ||
      !blowup.comparison.ranks_returned || blowup.comparison.betti[2] != 2 ||
      blowup.comparison.hodge[1][1] != 2 ||
      !rational(blowup.polarization.primitive[0], 1) ||
      !rational(blowup.polarization.primitive[1], 2) ||
      !rational(blowup.polarization.primitive_negative[0], 3) ||
      !rational(blowup.polarization.primitive_negative[1], -2) ||
      !rational(blowup.polarization.primitive_square, -8);
  failures += !value.foils.nonprimitive_rejected || !value.foils.nonsmooth_rejected ||
      !value.foils.incomplete_rejected || !value.foils.false_integral_lift_rejected ||
      !value.foils.incompatible_response_rejected ||
      !value.foils.wrong_subdivision_rejected ||
      !value.foils.principal_not_zero_support ||
      !value.foils.congruence_not_operator_conjugacy ||
      !value.foils.equal_class_not_equal_support ||
      value.foils.retained_principal[0] != 1 ||
      value.foils.retained_principal[2] != -1 ||
      !rational(value.foils.retained_incompatible_residual[0], 1) ||
      !rational(value.foils.retained_incompatible_residual[2], 0) ||
      value.foils.retained_wrong_ray.x != 2 || value.foils.retained_wrong_ray.y != 1;
  return failures;
}

}  // namespace

std::size_t r23_verification_failures(
    const apparatus::toric_store_receipt& card_load,
    const apparatus::toric_store_receipt& rest_load,
    const apparatus::toric_executor_receipt& execution,
    const apparatus::toric_probe_receipt& probe,
    const organ::toric_cycle_receipt& changed,
    const event::toric_cycle_observation& actual,
    const event::toric_cycle_rest_record& handoff) noexcept {
  const auto& inquiry = actual.inquiry;
  std::size_t failures = !card_load.returned() || !rest_load.returned() ||
      !execution.returned() || !probe.returned() ||
      execution.host_semantic_events != exact::word{0} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += inquiry.obstruction != organ::toric_obstruction::none ||
      !inquiry.no_expected_names || !inquiry.alternatives_retained ||
      !inquiry.all_exact || !inquiry.theory_formed;
  failures += fan_failures(inquiry) + realization_failures(inquiry) +
      blowup_failures(inquiry);
  failures += changed.realizations[0].state != organ::toric_realization_state::integral ||
      !rational(changed.realizations[0].class_coordinates[0], 2) ||
      !rational(changed.realizations[0].class_coordinates[1], 4) ||
      rational(changed.realizations[0].class_coordinates[1], 3) ||
      !changed.all_exact;
  const auto& passage = actual.passage;
  failures += passage.checker_stage != event::checker_stage_status::exact ||
      passage.typed.state != event::checker_return_status::accepted ||
      passage.typed.produced_declarations != 1 || passage.typed.remaining_goal_count != 0 ||
      !passage.typed.elaborator_boundary_crossed || !passage.typed.kernel_boundary_crossed ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 ||
      passage.raw.stderr_bytes != 0 || passage.raw.produced_artifact_bytes == 0 ||
      !passage.pending_before_process || passage.pending_after_return ||
      !passage.passage_preserved ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "theorem generated_toric_cycle_transport") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, ").den = 2") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'018} ||
      passage.formation_commit.successor != exact::word{14'001'019} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'020} ||
      passage.returned_morphology.mathematical_after != 116 ||
      passage.returned_morphology.codec_after != 63;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      !actual.remount.same_body || !actual.remount.theory_preserved ||
      actual.remount.source_replayed || !actual.handoff.returned ||
      !actual.final_can_continue || actual.final_head != exact::word{14'001'020} ||
      actual.final_continuation != exact::word{15'001'020};
  failures += handoff.integrity != event::toric_cycle_rest_integrity(handoff) ||
      handoff.body.regions[0].admitted_tally != 366 ||
      handoff.mathematical_admitted_tally != 116 || handoff.codec_admitted_tally != 63 ||
      handoff.cm_incidence_admitted_tally != 17 || handoff.toric_cycle_admitted_tally != 19 ||
      handoff.toric_cycle.identity != exact::word{190'300} ||
      !handoff.toric_cycle.accepted || !handoff.cm_incidence.accepted;
  return failures;
}

}  // namespace holonics::tests
