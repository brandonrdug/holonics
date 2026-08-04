#pragma once

#include <holonics/organ/regular_singular_schema.hpp>

namespace holonics::organ {

struct regular_singular_chart_receipt final {
  exact::word identity{};
  exact::word chart{};
  matrix_two residue{};
  matrix_two nilpotent{};
  std::int64_t trace{};
  std::int64_t determinant{};
  std::int64_t characteristic_discriminant{};
  std::int64_t lower_eigenvalue{};
  std::int64_t upper_eigenvalue{};
  std::int64_t right_eigenvector[2]{};
  std::int64_t generalized_vector[2]{};
  std::int64_t recurrence_image[2]{};
  std::int64_t recurrence_cokernel[2]{};
  std::int64_t resonant_source[2]{};
  std::int64_t obstruction_scalar{};
  std::int16_t scalar_indicial[3]{};
  std::uint64_t lineage{};
  std::uint8_t eigenvalue_gap{};
  std::uint8_t eigenflag_dimension{};
  std::uint8_t nilpotent_rank{};
  bool resonance_checked{};
  bool logarithmic_channel{};
  bool exact{};
};

struct frobenius_term_receipt final {
  exact::word identity{};
  std::uint16_t degree{};
  std::int64_t zero_numerator{};
  std::int64_t zero_denominator{};
  std::int64_t one_regular{};
  std::int64_t one_logarithmic{};
  std::int64_t zero_step_lhs{};
  std::int64_t zero_step_rhs{};
  std::int64_t one_step_residual{};
  std::uint64_t lineage{};
  bool exact{};
};

struct chamber_connection_receipt final {
  matrix_two zero_to_one{};
  matrix_two one_to_zero{};
  period_matrix_two monodromy_zero{};
  period_matrix_two monodromy_one{};
  period_matrix_two monodromy_infinity{};
  period_matrix_two loop_product{};
  period_matrix_two one_loop_in_zero_basis{};
  exact::word zero_basis{};
  exact::word one_basis{};
  exact::word overlap_path{};
  exact::word zero_loop{};
  exact::word one_loop{};
  exact::word infinity_loop{};
  std::uint64_t connection_lineage{};
  std::uint64_t loop_lineages[3]{};
  std::uint64_t loop_lineage{};
  std::int8_t connection_determinant{};
  std::uint8_t zero_fixed_dimension{};
  std::uint8_t one_fixed_dimension{};
  std::uint8_t infinity_fixed_dimension{};
  std::uint8_t one_nilpotent_rank{};
  std::uint8_t infinity_nilpotent_rank{};
  bool inverse_exact{};
  bool conjugacy_exact{};
  bool punctured_sphere_product_exact{};
  bool period_symbolic{};
  bool exact{};
};

struct regular_singular_receipt final {
  regular_singular_question question{};
  gauss_operator mounted_operator{};
  fuchsian_system system{};
  regular_singular_chart_receipt charts[regular_singular_chart_capacity]{};
  frobenius_term_receipt terms[regular_singular_term_capacity]{};
  chamber_connection_receipt connection{};
  regular_singular_theory_plan theory{};
  regular_singular_obstruction obstruction{regular_singular_obstruction::invalid_foundation};
  std::uint16_t returned_charts{};
  std::uint16_t returned_terms{};
  std::uint16_t logarithmic_charts{};
  bool no_special_function_lookup{};
  bool no_numerical_continuation{};
  bool no_expected_logarithm{};
  bool no_expected_eigenvector{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
