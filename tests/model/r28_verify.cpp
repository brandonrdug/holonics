#include "r28_verify.hpp"

namespace holonics::tests {
namespace {

template<std::size_t Capacity, class Count, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], Count used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t width = Pattern - 1U;
  for (std::size_t start = 0; width != 0 && start + width <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < width; ++slot) { same = same && bytes[start + slot] == pattern[slot]; }
    if (same) { return true; }
  }
  return false;
}

[[nodiscard]] std::size_t mathematical_failures(
    const event::hodge_realization_observation& actual) noexcept {
  const auto& value = actual.inquiry; std::size_t failures = !value.all_exact ||
      !value.theory_formed || !value.no_expected_invariants || !value.alternatives_retained ||
      value.obstruction != organ::hodge_realization_obstruction::none || !actual.changed_sensitive;
  for (const auto& factor : value.factors) {
    failures += !factor.exact || !factor.source_derived || !factor.roots_exact ||
        !factor.discriminant_exact || !factor.smooth_base || !factor.connection_exact ||
        factor.discriminant.coefficients[0] != 0 || factor.discriminant.coefficients[1] != 0 ||
        factor.discriminant.coefficients[2] != 1 || factor.discriminant.coefficients[3] != -2 ||
        factor.discriminant.coefficients[4] != 1;
  }
  const auto& product = value.product;
  failures += !product.exact || !product.cup_nondegenerate || !product.polarization_square_two ||
      !product.connection_t_preserves_cup || !product.connection_u_preserves_cup ||
      !product.mixed_curvature_zero || !product.griffiths_transverse ||
      !product.standard_comparison_boundary || product.common_denominator != -4 ||
      product.rational_rank != 6 || product.f2_rank != 1 || product.f1_rank != 5 ||
      product.h20 != 1 || product.h11 != 4 || product.h02 != 1;
  const auto& cycles = value.cycles;
  failures += !cycles.exact || !cycles.translations_distinct || !cycles.graph_relation_exact ||
      !cycles.rational_integral_separated || !cycles.alternatives_retained ||
      cycles.generator_count != 7 || cycles.image_rank != 3 || !cycles.locus.exact ||
      cycles.locus.quotient_obstruction[0] != -1 || cycles.locus.quotient_obstruction[1] != 1 ||
      cycles.locus.tangent_obstruction != 0 || cycles.locus.normal_obstruction != 1 ||
      cycles.locus.multiplicity != 1 || cycles.locus.graph_square != 0 ||
      cycles.locus.negation_square != 0 || cycles.locus.mutual_intersection != 4 ||
      cycles.locus.primitive_square != -2;
  for (const auto& translation : cycles.translations) {
    failures += !translation.exact || !translation.curve_identity || !translation.involution ||
        !translation.differential_pullback_identity || !translation.distinct_support ||
        !translation.h1_identity;
  }
  failures += cycles.fibers[0].enumerated != 2187 || cycles.fibers[0].realizer_count != 16 ||
      cycles.fibers[0].effective_count != 4 || !cycles.fibers[0].integral_member ||
      cycles.fibers[1].enumerated != 2187 || cycles.fibers[1].realizer_count != 16 ||
      cycles.fibers[1].integral_member || cycles.fibers[2].enumerated != 2187 ||
      !cycles.fibers[2].outside_image;
  const auto& blowup = value.blowup;
  failures += !blowup.exact || blowup.rank != 7 || blowup.kernel_rank != 1 ||
      !blowup.exceptional_square_minus_one || !blowup.pull_push_identity ||
      !blowup.projection_formula || !blowup.mapping_cone_residual_exact ||
      !blowup.all_push_to_graph || blowup.center_selector != 0 ||
      blowup.self_intersections[0] != -1 || blowup.self_intersections[1] != 0 ||
      !actual.changed.exact || actual.changed.center_selector != 1 ||
      actual.changed.self_intersections[0] != 0 || actual.changed.self_intersections[1] != -1;
  return failures;
}

}  // namespace

std::size_t r28_verification_failures(bool source_loaded,
    const apparatus::hodge_store_receipt& rest_load,
    const apparatus::hodge_executor_receipt& execution,
    const event::hodge_realization_observation& actual,
    const event::hodge_realization_rest_record& handoff) noexcept {
  std::size_t failures = !source_loaded || !rest_load.returned() || !execution.returned() ||
      execution.host_semantic_events != exact::word{0} ||
      execution.semantic_threads != exact::word{15} ||
      execution.kernel_launches != exact::word{11} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += mathematical_failures(actual); const auto& passage = actual.passage;
  failures += passage.checker_stage != event::checker_stage_status::exact ||
      passage.typed.state != event::checker_return_status::accepted ||
      passage.typed.produced_declarations != 1 || passage.typed.remaining_goal_count != 0 ||
      !passage.typed.elaborator_boundary_crossed || !passage.typed.kernel_boundary_crossed ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 || passage.raw.stderr_bytes != 0 ||
      passage.raw.produced_artifact_bytes == 0 || !passage.pending_before_process ||
      passage.pending_after_return || !passage.passage_preserved ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "theorem generated_hodge_realization") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "transportStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "filtrationStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "translationStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "locusStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "graphClassStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "blowupStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "blowupMapStatement") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'028} ||
      passage.formation_commit.successor != exact::word{14'001'029} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'030} ||
      passage.returned_morphology.mathematical_after != 207 ||
      passage.returned_morphology.codec_after != 103;
  failures += !actual.rest.returned || !actual.rest.source_detached || !actual.remount.same_body ||
      !actual.remount.theory_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.final_can_continue ||
      actual.final_head != exact::word{14'001'030} ||
      actual.final_continuation != exact::word{15'001'030};
  failures += handoff.integrity != event::hodge_realization_rest_integrity(handoff) ||
      handoff.body.regions[0].morphology != 693 || handoff.mathematical_morphology != 207 ||
      handoff.codec_morphology != 103 || handoff.expression_geometry_morphology != 37 ||
      handoff.hodge_realization_morphology != 41 ||
      handoff.hodge_realization.identity != exact::word{195'300} ||
      !handoff.hodge_realization.accepted || !handoff.expression_geometry.accepted;
  return failures;
}

}  // namespace holonics::tests
