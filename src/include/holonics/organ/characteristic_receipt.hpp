#pragma once

#include <holonics/organ/characteristic_schema.hpp>

namespace holonics::organ {

struct characteristic_case_receipt final {
  exact::word identity{};
  phase_case_definition definition{};
  std::uint16_t gcd{};
  std::uint16_t lcm{};
  std::uint16_t vertices{};
  std::uint16_t tours{};
  std::uint16_t tour_length{};
  std::uint16_t characteristic_degree{};
  std::uint16_t minimal_degree{};
  std::uint16_t mode_multiplicity{};
  std::uint16_t shape_types{};
  std::uint16_t shape_tour_classes{};
  std::uint16_t shape_exponent_total{};
  std::uint16_t shape_exponents[characteristic_tour_capacity]
      [characteristic_shape_capacity]{};
  std::uint64_t shape_tour_folds[characteristic_tour_capacity]{};
  bool orbit_exact{};
  bool characteristic_factor_exact{};
  bool minimal_factor_exact{};
  bool cycle_factor_squarefree{};
  bool global_discriminant_zero{};
  bool local_transport_singular{};
  bool formal_shape_transport_exact{};
  bool exact{};
};

struct scalar_cycle_control final {
  std::uint64_t first_product{};
  std::uint64_t second_product{};
  std::uint64_t first_lineage{};
  std::uint64_t second_lineage{};
  std::uint16_t length{};
  bool characteristic_equal{};
  bool lineage_distinct{};
  bool exact{};
};

struct matrix_control_receipt final {
  matrix_two first_word[3]{};
  matrix_two second_word[3]{};
  matrix_two ordered_first{};
  matrix_two ordered_second{};
  matrix_two rechart_source{};
  matrix_two rechart_target{};
  matrix_two rechart{};
  matrix_two rechart_inverse{};
  matrix_two independent_return{};
  matrix_two coupled_return{};
  std::uint64_t first_lineage{};
  std::uint64_t second_lineage{};
  std::uint64_t rechart_lineage{};
  std::int64_t first_trace{};
  std::int64_t second_trace{};
  std::int64_t first_determinant{};
  std::int64_t second_determinant{};
  std::int64_t rechart_trace{};
  std::int64_t rechart_determinant{};
  std::uint8_t independent_fixed_dimension{};
  std::uint8_t coupled_fixed_dimension{};
  bool order_changes_characteristic{};
  bool order_lineage_distinct{};
  bool rechart_preserves_characteristic{};
  bool equal_characteristic_unequal_conduct{};
  bool exact{};
};

struct indicial_receipt final {
  std::int16_t zero_coefficients[3]{};
  std::int16_t one_coefficients[3]{};
  std::int16_t infinity_coefficients[3]{};
  bool zero_roots_zero_negative_one{};
  bool one_repeated_zero{};
  bool infinity_repeated_one{};
  bool recurrence_is_only_one_local_branch{};
  bool exact{};
};

struct characteristic_receipt final {
  characteristic_question question{};
  characteristic_case_receipt cases[characteristic_case_capacity]{};
  scalar_cycle_control scalar{};
  matrix_control_receipt matrices{};
  indicial_receipt indicial{};
  characteristic_theory_plan theory{};
  characteristic_obstruction obstruction{characteristic_obstruction::invalid_foundation};
  std::uint16_t returned_cases{};
  std::uint16_t repeated_mode_cases{};
  std::uint16_t simple_mode_cases{};
  std::uint16_t shape_tour_classes{};
  bool no_expected_eigenvalue{};
  bool no_prime_mode_label{};
  bool no_renderer_source{};
  bool all_cases_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
