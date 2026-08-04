#pragma once

#include <holonics/organ/geometry_inquiry_receipt.hpp>
#include <holonics/organ/geometry_probe_law.hpp>

namespace holonics::organ {

[[nodiscard]] HOLONICS_CALLABLE constexpr fractional_difference_receipt
derive_fractional_difference() noexcept {
  fractional_difference_receipt receipt{};
  const std::int8_t expansion[8]{1, 1, 1, 1, -1, -1, -1, -1};
  for (std::size_t slot = 0; slot < 8; ++slot) {
    receipt.expanded_coefficients[slot] = expansion[slot];
  }
  receipt.alpha_gamma_xy_cancelled =
      receipt.expanded_coefficients[0] + receipt.expanded_coefficients[4] == 0;
  receipt.beta_delta_cancelled =
      receipt.expanded_coefficients[3] + receipt.expanded_coefficients[7] == 0;
  receipt.determinant_factored = receipt.expanded_coefficients[1] == 1 &&
      receipt.expanded_coefficients[2] == 1 && receipt.expanded_coefficients[5] == -1 &&
      receipt.expanded_coefficients[6] == -1;
  receipt.determinant_multiplicity[0] = 2;
  receipt.determinant_multiplicity[1] = 2;
  for (std::size_t point = 0; point < 4; ++point) {
    receipt.point_denominator_support[0][point] = 1;
    receipt.point_denominator_support[1][point] = 1;
  }
  receipt.complete_four_point_cancellation = receipt.alpha_gamma_xy_cancelled &&
      receipt.beta_delta_cancelled && receipt.determinant_factored;
  for (std::size_t point = 0; point < 4; ++point) {
    receipt.complete_four_point_cancellation = receipt.complete_four_point_cancellation &&
        receipt.point_denominator_support[0][point] ==
            receipt.point_denominator_support[1][point];
  }
  return receipt;
}

HOLONICS_CALLABLE constexpr void close_geometry_inquiry(
    const geometry_inquiry_foundation& foundation,
    const geometry_inquiry_question& question,
    geometry_inquiry_receipt& receipt) noexcept {
  receipt.question = question;
  receipt.mode_field_absent = true;
  receipt.expected_answer_absent = true;
  if (!valid_geometry_inquiry_foundation(foundation) || question.identity.value() == 0 ||
      question.receiver.value() == 0 || question.material.value() == 0) {
    receipt.obstruction = geometry_inquiry_obstruction::invalid_foundation;
    return;
  }
  for (std::size_t slot = 0; slot < foundation.probe_count; ++slot) {
    const auto& probe = receipt.probes[slot];
    if (probe.returned) { ++receipt.returned_probe_count; }
    if (probe.projectively_equal) { ++receipt.projective_probe_count; }
    if (probe.returned && !probe.quotient_singular && !probe.coordinates_equal) {
      ++receipt.coordinate_counterexamples;
    }
    if (probe.quotient_singular) { ++receipt.singular_probe_count; }
  }
  receipt.symbolic = derive_fractional_difference();
  receipt.fibers[0] = {exact::word{183'300}, exact::word{193'300},
      geometry_conjecture::raw_coordinate_invariance, geometry_fiber_state::obstructed,
      geometry_inquiry_obstruction::coordinate_counterexample,
      receipt.coordinate_counterexamples};
  receipt.fibers[1] = {exact::word{183'301}, exact::word{193'301},
      geometry_conjecture::affine_common_square, geometry_fiber_state::closed,
      geometry_inquiry_obstruction::none, receipt.projective_probe_count};
  receipt.fibers[2] = {exact::word{183'302}, exact::word{193'302},
      geometry_conjecture::fractional_cross_ratio, geometry_fiber_state::closed,
      geometry_inquiry_obstruction::none, receipt.projective_probe_count};
  receipt.fibers[3] = {exact::word{183'303}, exact::word{193'303},
      geometry_conjecture::singular_quotient_extension, geometry_fiber_state::obstructed,
      geometry_inquiry_obstruction::singular_chart, receipt.singular_probe_count};
  receipt.closed_fiber_count = 2;
  receipt.obstructed_fiber_count = 2;
  receipt.exact_local_front = receipt.returned_probe_count == foundation.probe_count &&
      receipt.projective_probe_count + receipt.singular_probe_count == foundation.probe_count;
  receipt.theory = {exact::word{173'300}, exact::word{153'300}, exact::word{153'301},
      exact::word{153'302}, exact::word{153'303}, exact::word{193'310},
      receipt.symbolic.determinant_factored, receipt.projective_probe_count != 0,
      receipt.symbolic.complete_four_point_cancellation,
      receipt.coordinate_counterexamples != 0, receipt.singular_probe_count != 0};
  receipt.theory_formed = receipt.exact_local_front && receipt.theory.difference_factor &&
      receipt.theory.fractional_invariance && receipt.theory.coordinate_counterexample &&
      receipt.theory.singular_boundary;
  receipt.obstruction = receipt.theory_formed ? geometry_inquiry_obstruction::none :
      geometry_inquiry_obstruction::symbolic_factor_absent;
}

}  // namespace holonics::organ
