#pragma once

#include <holonics/organ/algebraic_variation_schema.hpp>

namespace holonics::organ {

struct parameter_polynomial final {
  std::int64_t coefficients[variation_polynomial_capacity]{};
  std::uint8_t degree{};
  bool exact{};
};

struct affine_root_section final {
  affine_integer_coefficient root{};
  exact::word identity{};
  exact::word lineage{};
  bool coefficientwise_zero{};
};

struct variation_collision_receipt final {
  exact::small_rational parameter{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t left{};
  std::uint8_t right{};
  std::uint8_t multiplicity{};
  bool ordered{};
  bool exact{};
};

struct differential_reduction_receipt final {
  exact::small_rational connection[2]{};
  exact::small_rational witness[3]{};
  exact::word identity{};
  exact::word lineage{};
  bool coefficient_residual_zero{};
  bool exact{};
};

struct variation_sample_receipt final {
  exact::small_rational parameter{};
  exact::small_rational discriminant{};
  exact::small_rational connection[2][2]{};
  differential_reduction_receipt reductions[2]{};
  exact::word identity{};
  exact::word lineage{};
  bool discovery{};
  bool holdout{};
  bool regular{};
  bool singular{};
  bool exact{};
};

struct global_connection_receipt final {
  affine_integer_coefficient numerator[2][2]{};
  parameter_polynomial pole_polynomial{};
  affine_integer_coefficient witness_numerator[2][3]{};
  std::int64_t denominator_scale{};
  exact::word identity{};
  exact::word lineage{};
  bool discovery_only{};
  bool holdouts_exact{};
  bool symbolic_residual_zero{};
  bool pole_support_matches_discriminant{};
  bool exact{};
};

struct invariant_form_candidate final {
  std::int64_t form[2][2]{};
  exact::small_rational residual[2][2]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint16_t first_failed_sample{};
  bool primitive{};
  bool discovery_exact{};
  bool holdout_exact{};
  bool orientation_selected{};
};

struct invariant_form_receipt final {
  invariant_form_candidate candidates[variation_candidate_capacity]{};
  std::int64_t selected[2][2]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint32_t enumerated{};
  std::uint32_t discovery_survivors{};
  std::uint8_t retained_count{};
  bool orientation_founded{};
  bool exact{};
};

struct scalar_operator_receipt final {
  std::int64_t second[3]{};
  std::int64_t first[2]{};
  std::int64_t zeroth{};
  exact::small_rational series[variation_series_capacity]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t constraint_rank{};
  std::uint8_t series_count{};
  bool discovery_only{};
  bool holdouts_exact{};
  bool primitive{};
  bool recurrence_exact{};
  bool exact{};
};

struct loop_transport_receipt final {
  std::int64_t vanishing_cycles[2][2]{};
  std::int64_t monodromy[3][2][2]{};
  std::int64_t loop_product[2][2]{};
  exact::word identities[3]{};
  exact::word lineages[3]{};
  std::uint8_t twist_weight{};
  bool standard_hypotheses{};
  bool pairing_preserved{};
  bool ordered_product_identity{};
  bool noncommuting{};
  bool unequal_collision_lineage{};
  bool exact{};
};

enum class theorem_candidate_state : std::uint8_t {
  incomplete_dependency,
  holdout_refused,
  foil_refused,
  selected
};

struct theorem_candidate_section final {
  exact::word identity{};
  exact::word lineage{};
  std::uint16_t dependency_mask{};
  std::uint16_t residual_mask{};
  theorem_candidate_state state{theorem_candidate_state::incomplete_dependency};
};

struct theorem_selection_receipt final {
  theorem_candidate_section candidates[4]{};
  exact::word selected{};
  exact::word lineage{};
  std::uint8_t candidate_count{};
  bool no_score{};
  bool no_expected_statement{};
  bool holdout_closed{};
  bool foils_closed{};
  bool exact{};
};

struct variation_foil_receipt final {
  exact::small_rational euclidean_residual[2][2]{};
  exact::small_rational symmetric_residual[2][2]{};
  exact::small_rational degenerate_residual[2][2]{};
  bool squarefree_multiplicity_rejected{};
  bool local_only_form_rejected{};
  bool euclidean_form_rejected{};
  bool symmetric_form_rejected{};
  bool degenerate_form_rejected{};
  bool operator_without_zeroth_rejected{};
  bool commuting_loops_rejected{};
  bool equal_spectrum_not_equal_collision{};
};

struct algebraic_variation_receipt final {
  algebraic_variation_card mounted{};
  algebraic_variation_question question{};
  parameter_polynomial discriminant{};
  parameter_polynomial vandermonde_square{};
  affine_root_section roots[variation_root_capacity]{};
  variation_collision_receipt collisions[variation_collision_capacity]{};
  variation_sample_receipt samples[variation_sample_capacity]{};
  global_connection_receipt connection{};
  invariant_form_receipt invariant{};
  scalar_operator_receipt scalar{};
  loop_transport_receipt loops{};
  theorem_selection_receipt selection{};
  variation_foil_receipt foils{};
  algebraic_variation_plan theory{};
  variation_obstruction obstruction{variation_obstruction::invalid_foundation};
  std::uint8_t root_count{};
  std::uint8_t collision_count{};
  bool discriminant_exact{};
  bool roots_exact{};
  bool alternatives_retained{};
  bool no_expected_names{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
