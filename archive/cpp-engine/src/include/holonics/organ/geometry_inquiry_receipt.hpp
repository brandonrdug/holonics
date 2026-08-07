#pragma once

#include <holonics/organ/geometry_inquiry_schema.hpp>

namespace holonics::organ {

struct geometry_probe_receipt final {
  exact::word identity{};
  exact::word points[4]{};
  exact::word frame[4]{};
  inquiry_ratio_pair original{};
  inquiry_ratio_pair transformed{};
  exact::word determinant{};
  exact::word common_square{};
  bool projectively_equal{};
  bool coordinates_equal{};
  bool quotient_singular{};
  bool returned{};
};

struct fractional_difference_receipt final {
  std::int8_t expanded_coefficients[8]{};
  std::uint8_t point_denominator_support[2][4]{};
  std::uint8_t determinant_multiplicity[2]{};
  bool alpha_gamma_xy_cancelled{};
  bool beta_delta_cancelled{};
  bool determinant_factored{};
  bool complete_four_point_cancellation{};
};

struct geometry_inquiry_receipt final {
  geometry_inquiry_question question{};
  geometry_probe_receipt probes[geometry_inquiry_probe_capacity]{};
  fractional_difference_receipt symbolic{};
  geometry_conjecture_fiber fibers[geometry_inquiry_fiber_capacity]{};
  geometry_theory_plan theory{};
  geometry_inquiry_obstruction obstruction{geometry_inquiry_obstruction::invalid_foundation};
  std::uint16_t returned_probe_count{};
  std::uint16_t projective_probe_count{};
  std::uint16_t coordinate_counterexamples{};
  std::uint16_t singular_probe_count{};
  std::uint16_t closed_fiber_count{};
  std::uint16_t obstructed_fiber_count{};
  std::uint16_t global_candidate_scans{};
  bool exact_local_front{};
  bool mode_field_absent{};
  bool expected_answer_absent{};
  bool theory_formed{};
};

}  // namespace holonics::organ
