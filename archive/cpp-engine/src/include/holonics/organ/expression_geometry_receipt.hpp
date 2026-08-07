#pragma once

#include <holonics/exact/small_rational.hpp>
#include <holonics/organ/expression_geometry_schema.hpp>

namespace holonics::organ {

struct expression_parameter_polynomial final {
  std::int64_t coefficients[expression_parameter_capacity]{};
  std::uint8_t degree{};
  bool exact{};
};

struct expression_reduction_step final {
  exact::word identity{};
  exact::word lineage{};
  std::int64_t coefficient{};
  std::uint8_t source{};
  std::uint8_t target{};
  std::uint8_t parameter_power{};
  std::uint8_t x_power{};
  std::uint8_t y_power{};
  bool residual_zero{};
};

struct expression_ideal_receipt final {
  sparse_expression partials[3]{};
  sparse_expression basis[3]{};
  expression_reduction_step reductions[expression_reduction_capacity]{};
  expression_parameter_polynomial resultant{};
  expression_parameter_polynomial bezout_f[4]{};
  expression_parameter_polynomial bezout_fx[5]{};
  std::int64_t resultant_samples[9]{};
  exact::word identity{};
  exact::word lineage{};
  std::int64_t constant_parameter{};
  std::int8_t chart_shift{};
  std::uint16_t resultant_content{};
  std::uint16_t resultant_sample_mask{};
  std::uint16_t bezout_sample_mask{};
  std::uint8_t reduction_count{};
  std::uint8_t geometric_singular_count{};
  bool lex_order_retained{};
  bool grevlex_order_retained{};
  bool spairs_closed{};
  bool syzygies_exact{};
  bool triangular_equivalent{};
  bool primitive{};
  bool squarefree{};
  bool rational_linear_factor_absent{};
  bool higher_factor_open{};
  bool cotangent_generic_rank_one{};
  bool singular_cotangent_dimension_two{};
  bool hessian_invertible{};
  bool exact{};
};

struct expression_reduction_witness final {
  exact::small_rational p[4]{};
  exact::small_rational q[5]{};
  exact::small_rational reduced[expression_basis_rank]{};
  exact::word identity{};
  exact::word lineage{};
  bool source_identity{};
  bool differential_identity{};
  bool exact{};
};

struct expression_differential_sample final {
  exact::small_rational parameter{};
  exact::small_rational discriminant{};
  expression_reduction_witness reductions[expression_basis_rank]{};
  exact::word identity{};
  exact::word lineage{};
  bool discovery{};
  bool holdout{};
  bool regular{};
  bool exact{};
};

struct expression_connection_receipt final {
  expression_parameter_polynomial numerator[expression_basis_rank][expression_basis_rank]{};
  expression_parameter_polynomial reduction_p[expression_basis_rank][4]{};
  expression_parameter_polynomial reduction_q[expression_basis_rank][5]{};
  expression_parameter_polynomial denominator{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t rank{};
  bool basis_derived{};
  bool discovery_only{};
  bool coefficient_residual_zero{};
  bool holdouts_exact{};
  bool exact{};
};

struct expression_scalar_receipt final {
  expression_parameter_polynomial coefficients[5]{};
  exact::small_rational series[expression_basis_rank][expression_series_capacity]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t order{};
  std::uint8_t series_count{};
  bool cyclic_vector_exact{};
  bool primitive{};
  bool recurrence_exact{};
  bool holdouts_exact{};
  bool exact{};
};

struct expression_indicial_receipt final {
  std::int64_t finite_coefficients[5]{};
  std::int64_t infinity_coefficients[5]{};
  exact::small_rational finite_roots[4]{};
  exact::small_rational infinity_roots[4]{};
  exact::word identity{};
  exact::word lineage{};
  bool finite_factored{};
  bool infinity_factored{};
  bool repeated_finite_root{};
  bool regular_singular{};
  bool exact{};
};

struct expression_algebraic_value final {
  exact::small_rational coefficients[expression_residue_degree]{};
};

struct expression_residue_receipt final {
  expression_algebraic_value matrix[expression_basis_rank][expression_basis_rank]{};
  exact::word identity{};
  exact::word lineage{};
  std::int64_t relation_constant{};
  bool nonzero{};
  bool all_two_minors_zero{};
  bool square_zero{};
  bool rank_one{};
  bool logarithmic_channel{};
  bool exact{};
};

struct expression_presentation_receipt final {
  sparse_expression mounted{};
  expression_ideal_receipt ideal{};
  expression_differential_sample samples[expression_sample_capacity]{};
  expression_connection_receipt connection{};
  expression_scalar_receipt scalar{};
  expression_indicial_receipt indicial{};
  expression_residue_receipt residue{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t sample_count{};
  bool exact{};
};

struct expression_rechart_receipt final {
  exact::word source{};
  exact::word target{};
  exact::word lineage{};
  std::int8_t x_scale{};
  std::int8_t x_shift{};
  std::int8_t y_square{};
  std::int8_t equation_scale{};
  bool rational{};
  bool gaussian{};
  bool expression_identity{};
  bool geometry_identity{};
  bool field_dependency_retained{};
  bool exact{};
};

struct expression_fiber_receipt final {
  exact::word invariant{};
  exact::word members[expression_presentation_capacity]{};
  std::uint8_t member_count{};
  bool rational_members_separated{};
  bool complete{};
};

struct expression_control_receipt final {
  bool translated_support_changed{};
  bool rational_rechart_exact{};
  bool equal_discriminant_not_rational_identity{};
  bool gaussian_extension_exact{};
  bool equal_scalar_fiber_retained{};
  bool changed_source_sensitive{};
  bool exact{};
};

struct expression_changed_receipt final {
  expression_presentation_receipt presentations[2]{};
  expression_rechart_receipt rechart{};
  bool discriminant_changed{};
  bool series_changed{};
  bool source_sensitive{};
  bool exact{};
};

struct expression_geometry_receipt final {
  expression_geometry_card mounted{};
  expression_geometry_question question{};
  expression_presentation_receipt presentations[expression_presentation_capacity]{};
  expression_rechart_receipt rational_rechart{};
  expression_rechart_receipt gaussian_rechart{};
  expression_fiber_receipt invariant_fiber{};
  expression_control_receipt controls{};
  expression_geometry_plan theory{};
  expression_geometry_obstruction obstruction{expression_geometry_obstruction::invalid_foundation};
  bool no_expected_invariants{};
  bool alternatives_retained{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
