#pragma once

#include <holonics/organ/toric_cycle_schema.hpp>

namespace holonics::organ {

struct toric_fan_receipt final {
  exact::word identity{};
  toric_fan_card source{};
  std::int64_t cone_determinants[toric_ray_capacity]{};
  std::int64_t character_map[2][toric_ray_capacity]{};
  std::int64_t smith_invariants[2]{};
  std::uint64_t lineage{};
  std::uint8_t cone_count{};
  bool primitive{};
  bool smooth{};
  bool complete{};
  bool character_exact{};
};

struct toric_quotient_receipt final {
  exact::word identity{};
  toric_rational divisor_classes[toric_ray_capacity][toric_rank_capacity]{};
  std::int64_t basis_lifts[toric_rank_capacity][toric_ray_capacity]{};
  std::int64_t principal_relations[2][toric_ray_capacity]{};
  std::uint64_t lineage{};
  std::uint8_t rank{};
  std::uint8_t relation_rank{};
  std::uint8_t torsion_count{};
  bool smith_exact{};
  bool torsion_free{};
  bool exact{};
};

struct toric_intersection_receipt final {
  exact::word identity{};
  toric_rational fan_divisor_form[toric_ray_capacity][toric_ray_capacity]{};
  toric_rational chow_divisor_form[toric_ray_capacity][toric_ray_capacity]{};
  toric_rational quotient_form[toric_rank_capacity][toric_rank_capacity]{};
  toric_rational congruence_basis[toric_rank_capacity][toric_rank_capacity]{};
  toric_rational congruence_form[toric_rank_capacity][toric_rank_capacity]{};
  toric_rational determinant{};
  toric_rational basis_determinant{};
  std::uint64_t lineage{};
  std::uint8_t rank{};
  std::uint8_t positive{};
  std::uint8_t negative{};
  std::uint8_t radical{};
  bool fan_chow_agree{};
  bool inertia_exact{};
  bool exact{};
};

struct toric_representative final {
  toric_rational coefficients[toric_ray_capacity]{};
  exact::word identity{};
  std::uint64_t lineage{};
  std::uint8_t support_mask{};
};

enum class toric_realization_state : std::uint8_t {
  integral,
  rational_only,
  incompatible
};

struct toric_realization_receipt final {
  exact::word identity{};
  toric_target target{};
  toric_rational class_coordinates[toric_rank_capacity]{};
  std::int64_t principal_kernel[2][toric_ray_capacity]{};
  toric_representative representatives[toric_representative_capacity]{};
  std::uint64_t lineage{};
  std::uint16_t representative_count{};
  std::uint8_t kernel_rank{};
  toric_realization_state state{toric_realization_state::incompatible};
  bool full_response_checked{};
  bool exact{};
};

struct toric_polarization_receipt final {
  exact::word identity{};
  toric_rational anticanonical[toric_rank_capacity]{};
  toric_rational primitive[toric_rank_capacity]{};
  toric_rational response[toric_ray_capacity]{};
  toric_rational primitive_negative[toric_rank_capacity]{};
  toric_rational primitive_square{};
  std::uint64_t lineage{};
  bool response_positive{};
  bool negative_control{};
  bool has_orthogonal_direction{};
  bool exact{};
};

struct toric_comparison_receipt final {
  exact::word identity{};
  std::uint64_t lineage{};
  std::uint8_t betti[5]{};
  std::uint8_t hodge[3][3]{};
  bool standard_hypotheses{};
  bool ranks_returned{};
};

struct toric_transform_receipt final {
  exact::word identity{};
  toric_rational strict[toric_rank_capacity]{};
  toric_rational total[toric_rank_capacity]{};
  std::uint64_t lineage{};
  std::uint8_t old_ray{};
  std::uint8_t new_ray{};
  bool exact{};
};

struct toric_blowup_receipt final {
  exact::word identity{};
  toric_integer_pair derived_ray{};
  toric_fan_receipt fan{};
  toric_quotient_receipt quotient{};
  toric_intersection_receipt intersection{};
  toric_polarization_receipt polarization{};
  toric_rational exceptional[toric_rank_capacity]{};
  toric_rational exceptional_square{};
  toric_rational pullback[toric_rank_capacity]{};
  toric_rational pushforward[toric_rank_capacity]{};
  toric_transform_receipt transforms[toric_ray_capacity]{};
  toric_rational pullback_matrix[toric_rank_capacity][toric_rank_capacity]{};
  toric_rational pushforward_matrix[toric_rank_capacity][toric_rank_capacity]{};
  toric_comparison_receipt comparison{};
  std::uint64_t lineage{};
  std::uint8_t old_ray_count{};
  std::uint8_t pullback_kernel_rank{};
  std::uint8_t pullback_image_rank{};
  std::uint8_t pushforward_kernel_rank{};
  std::uint8_t pushforward_image_rank{};
  bool projection_formula{};
  bool exact{};
};

struct toric_foil_receipt final {
  bool nonprimitive_rejected{};
  bool nonsmooth_rejected{};
  bool incomplete_rejected{};
  bool false_integral_lift_rejected{};
  bool incompatible_response_rejected{};
  bool wrong_subdivision_rejected{};
  bool principal_not_zero_support{};
  bool congruence_not_operator_conjugacy{};
  bool equal_class_not_equal_support{};
  std::int64_t retained_principal[toric_ray_capacity]{};
  toric_rational retained_incompatible_residual[toric_ray_capacity]{};
  toric_integer_pair retained_wrong_ray{};
};

struct toric_cycle_receipt final {
  toric_cycle_question question{};
  toric_cycle_card mounted{};
  toric_fan_receipt fans[toric_fan_capacity]{};
  toric_quotient_receipt quotients[toric_fan_capacity]{};
  toric_intersection_receipt intersections[toric_fan_capacity]{};
  toric_comparison_receipt comparisons[toric_fan_capacity]{};
  toric_realization_receipt realizations[toric_target_capacity]{};
  toric_polarization_receipt source_polarization{};
  toric_polarization_receipt polarization{};
  toric_blowup_receipt blowup{};
  toric_foil_receipt foils{};
  toric_cycle_plan theory{};
  toric_obstruction obstruction{toric_obstruction::invalid_foundation};
  bool no_expected_names{};
  bool alternatives_retained{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
