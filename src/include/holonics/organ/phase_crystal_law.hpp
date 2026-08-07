#pragma once

#include <holonics/organ/phase_crystal_probe_law.hpp>

namespace holonics::organ {
namespace phase_crystal_law_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_hull(
    const phase_case_receipt& left, const phase_case_receipt& right) noexcept {
  return left.hull_corners == right.hull_corners &&
      left.contracted_sides == right.contracted_sides &&
      left.hull_edge_types == right.hull_edge_types;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_ratio(
    phase_ratio left, phase_ratio right) noexcept {
  return left.numerator == right.numerator && left.denominator == right.denominator;
}

}  // namespace phase_crystal_law_detail

HOLONICS_CALLABLE constexpr void close_phase_crystal_inquiry(
    const phase_crystal_foundation& foundation,
    const phase_crystal_question& question,
    phase_crystal_receipt& receipt) noexcept {
  using namespace phase_crystal_detail;
  using namespace phase_crystal_law_detail;
  receipt.question = question;
  receipt.mode_field_absent = true;
  receipt.expected_shape_absent = true;
  receipt.historical_renderer_absent = true;
  if (!valid_phase_crystal_foundation(foundation) || question.identity.value() == 0 ||
      question.receiver.value() == 0 || question.material.value() == 0) {
    receipt.obstruction = phase_crystal_obstruction::invalid_foundation;
    return;
  }
  receipt.all_intrinsic_cells_exact = true;
  receipt.all_series_exact = true;
  for (std::uint16_t slot = 0; slot < foundation.case_count; ++slot) {
    const auto& value = receipt.cases[slot];
    receipt.returned_cases = static_cast<std::uint16_t>(receipt.returned_cases +
        (value.exact ? 1U : 0U));
    receipt.all_intrinsic_cells_exact = receipt.all_intrinsic_cells_exact && value.exact &&
        value.complete_boundary_cancels && value.orbit_partition_exact &&
        value.cell_population_factorized && !value.screen_crossings_are_contacts;
    receipt.all_series_exact = receipt.all_series_exact &&
        value.series_recurrence_exact && value.series_closed_form_detected;
    receipt.total_shape_types = static_cast<std::uint16_t>(
        receipt.total_shape_types + value.cell_shape_types);
    receipt.total_transition_types = static_cast<std::uint16_t>(
        receipt.total_transition_types + value.shape_transition_types);
    if (value.definition.kind == phase_case_kind::prime_pair) { ++receipt.prime_cases; }
    else { ++receipt.control_cases; }
    if (value.definition.kind == phase_case_kind::composite_coprime ||
        value.definition.kind == phase_case_kind::composite_shared_factor) {
      ++receipt.composite_cases;
    }
    if (value.definition.kind == phase_case_kind::composite_shared_factor) {
      ++receipt.shared_factor_cases;
    }
  }
  const auto& baseline = receipt.cases[3];
  const auto& reversed = receipt.cases[11];
  const auto& dilated = receipt.cases[12];
  const auto& turned = receipt.cases[13];
  const auto& reversed_pair = receipt.cases[14];
  phase_ratio expected_shortest{};
  phase_ratio expected_longest{};
  receipt.dilation_control_exact = same_hull(baseline, dilated) &&
      scale(baseline.receiver_shortest_hull_side, 625, 256, expected_shortest) &&
      scale(baseline.receiver_longest_hull_side, 625, 256, expected_longest) &&
      same_ratio(expected_shortest, dilated.receiver_shortest_hull_side) &&
      same_ratio(expected_longest, dilated.receiver_longest_hull_side);
  receipt.turn_control_exact = same_hull(baseline, turned) &&
      same_ratio(baseline.receiver_shortest_hull_side, turned.receiver_shortest_hull_side) &&
      same_ratio(baseline.receiver_longest_hull_side, turned.receiver_longest_hull_side);
  receipt.reversal_control_exact = same_hull(reversed, reversed_pair) &&
      same_ratio(reversed.receiver_shortest_hull_side,
          reversed_pair.receiver_shortest_hull_side) &&
      same_ratio(reversed.receiver_longest_hull_side,
          reversed_pair.receiver_longest_hull_side);
  receipt.theory = {exact::word{174'300}, exact::word{154'300}, exact::word{154'301},
      exact::word{154'302}, exact::word{154'303}, exact::word{194'300},
      receipt.all_intrinsic_cells_exact, receipt.shared_factor_cases == 2,
      receipt.total_shape_types != 0, receipt.all_intrinsic_cells_exact,
      receipt.all_series_exact, receipt.dilation_control_exact &&
          receipt.turn_control_exact && receipt.reversal_control_exact};
  receipt.theory_formed = receipt.returned_cases == foundation.case_count &&
      receipt.prime_cases == 7 && receipt.composite_cases == 5 &&
      receipt.shared_factor_cases == 2 && receipt.control_cases == 9 &&
      receipt.all_intrinsic_cells_exact && receipt.all_series_exact &&
      receipt.theory.diagonal_lcm && receipt.theory.coprime_full_tour &&
      receipt.theory.cell_population_product && receipt.theory.seam_cancellation &&
      receipt.theory.gauss_transport && receipt.theory.projection_distinguished;
  receipt.obstruction = receipt.theory_formed ? phase_crystal_obstruction::none :
      phase_crystal_obstruction::control_refused;
}

}  // namespace holonics::organ
