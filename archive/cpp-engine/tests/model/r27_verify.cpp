#include "r27_verify.hpp"

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

[[nodiscard]] std::size_t presentation_failures(
    const organ::expression_presentation_receipt& value) noexcept {
  std::size_t failures = !value.exact || !value.ideal.exact || !value.ideal.spairs_closed ||
      !value.ideal.syzygies_exact || !value.ideal.triangular_equivalent ||
      !value.ideal.squarefree || !value.ideal.rational_linear_factor_absent ||
      !value.ideal.higher_factor_open || !value.ideal.cotangent_generic_rank_one ||
      !value.ideal.singular_cotangent_dimension_two || !value.ideal.hessian_invertible ||
      value.ideal.geometric_singular_count != 5 || !value.connection.exact ||
      !value.connection.basis_derived || !value.connection.coefficient_residual_zero ||
      !value.connection.holdouts_exact || value.connection.rank != 4 ||
      !value.scalar.exact || value.scalar.order != 4 || !value.scalar.cyclic_vector_exact ||
      !value.scalar.recurrence_exact || value.scalar.series_count != 11 ||
      !value.indicial.exact || !value.indicial.finite_factored ||
      !value.indicial.infinity_factored || !value.indicial.repeated_finite_root ||
      !value.residue.exact || !value.residue.nonzero || !value.residue.rank_one ||
      !value.residue.all_two_minors_zero || !value.residue.square_zero ||
      !value.residue.logarithmic_channel || value.sample_count != 11;
  const std::int64_t finite[5]{0,0,2,-3,1};
  const std::int64_t infinity[5]{29601,114624,108416,36864,4096};
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    failures += value.indicial.finite_coefficients[slot] != finite[slot] ||
        value.indicial.infinity_coefficients[slot] != infinity[slot];
  }
  return failures;
}

[[nodiscard]] std::size_t canonical_failures(
    const organ::expression_presentation_receipt& value) noexcept {
  std::size_t failures = presentation_failures(value) +
      (value.ideal.resultant.coefficients[0] != 3125) +
      (value.ideal.resultant.coefficients[5] != -256) +
      (value.scalar.coefficients[4].coefficients[0] != 50000) +
      (value.scalar.coefficients[4].coefficients[5] != -4096) +
      (value.scalar.coefficients[3].coefficients[4] != -61440) +
      (value.scalar.coefficients[2].coefficients[3] != -247680) +
      (value.scalar.coefficients[1].coefficients[2] != -264000) +
      (value.scalar.coefficients[0].coefficients[1] != -29601);
  const std::int64_t coefficients[4][4]{{192,625,-500,-1200},
      {240,64,-625,-1500},{300,80,-64,-1875},{375,100,-80,-192}};
  const std::uint8_t degrees[4][4]{{4,0,1,2},{3,4,0,1},{2,3,4,0},{1,2,3,4}};
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      const auto& polynomial = value.connection.numerator[row][column];
      failures += polynomial.coefficients[degrees[row][column]] != coefficients[row][column];
    }
  }
  failures += !organ::expression_exact_detail::equal(value.scalar.series[0][5],
          {9867,2000000}) || !organ::expression_exact_detail::equal(
          value.scalar.series[1][6], {97867,6000000}) ||
      !organ::expression_exact_detail::equal(
          value.residue.matrix[0][0].coefficients[0], {-3,40});
  return failures;
}

[[nodiscard]] std::size_t mathematical_failures(
    const event::expression_geometry_observation& actual) noexcept {
  const auto& value = actual.inquiry; std::size_t failures = !value.all_exact ||
      !value.theory_formed || value.theory.source_mask != 7 || !value.no_expected_invariants ||
      !value.alternatives_retained || value.obstruction != organ::expression_geometry_obstruction::none;
  failures += canonical_failures(value.presentations[0]);
  failures += presentation_failures(value.presentations[1]);
  failures += presentation_failures(value.presentations[2]);
  failures += !value.rational_rechart.exact || !value.rational_rechart.rational ||
      value.rational_rechart.x_shift != 1 || !value.gaussian_rechart.exact ||
      !value.gaussian_rechart.gaussian || value.gaussian_rechart.x_scale != -1 ||
      value.gaussian_rechart.y_square != -1 || !value.gaussian_rechart.field_dependency_retained ||
      !value.invariant_fiber.complete || value.invariant_fiber.member_count != 3 ||
      !value.invariant_fiber.rational_members_separated || !value.controls.exact ||
      !value.controls.equal_discriminant_not_rational_identity ||
      !value.controls.equal_scalar_fiber_retained || !value.controls.changed_source_sensitive;
  const auto& changed = actual.changed;
  failures += !changed.exact || !actual.changed_sensitive || !changed.discriminant_changed ||
      !changed.series_changed || !changed.source_sensitive || !changed.rechart.exact ||
      presentation_failures(changed.presentations[0]) != 0 ||
      presentation_failures(changed.presentations[1]) != 0 ||
      changed.presentations[0].ideal.resultant.coefficients[0] != 50000 ||
      changed.presentations[0].ideal.resultant.coefficients[5] != -256 ||
      changed.presentations[0].scalar.coefficients[4].coefficients[0] != 800000 ||
      organ::expression_exact_detail::equal(changed.presentations[0].scalar.series[0][5],
          value.presentations[0].scalar.series[0][5]);
  return failures;
}

}  // namespace

std::size_t r27_verification_failures(bool source_loaded,
    const apparatus::expression_geometry_store_receipt& rest_load,
    const apparatus::expression_geometry_executor_receipt& execution,
    const event::expression_geometry_observation& actual,
    const event::expression_geometry_rest_record& handoff) noexcept {
  std::size_t failures = !source_loaded || !rest_load.returned() || !execution.returned() ||
      execution.host_semantic_events != exact::word{0} ||
      execution.semantic_threads != exact::word{7} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += mathematical_failures(actual); const auto& passage = actual.passage;
  failures += passage.checker_stage != event::checker_stage_status::exact ||
      passage.typed.state != event::checker_return_status::accepted ||
      passage.typed.produced_declarations != 1 || passage.typed.remaining_goal_count != 0 ||
      !passage.typed.elaborator_boundary_crossed || !passage.typed.kernel_boundary_crossed ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 || passage.raw.stderr_bytes != 0 ||
      passage.raw.produced_artifact_bytes == 0 || !passage.pending_before_process ||
      passage.pending_after_return || !passage.passage_preserved ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "theorem generated_expression_geometry") ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "x*(t-5*x^4)") ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "*(5*x^4-t)") ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "z0 z1 z2 z3 z4") ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "4*a^5=1") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'026} ||
      passage.formation_commit.successor != exact::word{14'001'027} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'028} ;
  failures += !actual.rest.returned || !actual.rest.source_detached || !actual.remount.same_body ||
      !actual.remount.theory_preserved || actual.remount.source_replayed ||
      !actual.handoff.returned || !actual.final_can_continue ||
      actual.final_head != exact::word{14'001'028} ||
      actual.final_continuation != exact::word{15'001'028};
  failures += handoff.integrity != event::expression_geometry_rest_integrity(handoff) ||
      handoff.expression_geometry.identity != exact::word{194'300} ||
      !handoff.expression_geometry.accepted || !handoff.intrinsic_hypergeometry.accepted;
  return failures;
}

}  // namespace holonics::tests
