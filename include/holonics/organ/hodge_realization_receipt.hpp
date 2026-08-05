#pragma once

#include <holonics/exact/small_rational.hpp>
#include <holonics/organ/algebraic_variation_receipt.hpp>
#include <holonics/organ/hodge_realization_schema.hpp>

namespace holonics::organ {

struct hodge_factor_receipt final {
  hodge_family_source mounted{};
  affine_root_section roots[3]{};
  parameter_polynomial discriminant{};
  affine_integer_coefficient connection[2][2]{};
  parameter_polynomial denominator{};
  std::int64_t alternating[2][2]{};
  exact::word identity{};
  exact::word lineage{};
  std::int64_t base_parameter{};
  bool source_derived{};
  bool roots_exact{};
  bool discriminant_exact{};
  bool smooth_base{};
  bool connection_exact{};
  bool exact{};
};

struct hodge_product_receipt final {
  exact::word basis[hodge_rank]{};
  std::int64_t cup[hodge_rank][hodge_rank]{};
  affine_integer_coefficient connection_t[hodge_rank][hodge_rank]{};
  affine_integer_coefficient connection_u[hodge_rank][hodge_rank]{};
  std::int64_t connection_t_base[hodge_rank][hodge_rank]{};
  std::int64_t connection_u_base[hodge_rank][hodge_rank]{};
  std::int64_t polarization[hodge_rank]{};
  std::uint8_t f2_basis[1]{};
  std::uint8_t f1_basis[5]{};
  exact::word identity{};
  exact::word lineage{};
  std::int64_t common_denominator{};
  std::uint8_t rational_rank{};
  std::uint8_t f2_rank{};
  std::uint8_t f1_rank{};
  std::uint8_t h20{};
  std::uint8_t h11{};
  std::uint8_t h02{};
  bool cup_nondegenerate{};
  bool polarization_square_two{};
  bool connection_t_preserves_cup{};
  bool connection_u_preserves_cup{};
  bool mixed_curvature_zero{};
  bool griffiths_transverse{};
  bool standard_comparison_boundary{};
  bool exact{};
};

struct hodge_locus_receipt final {
  std::int64_t graph_class[hodge_rank]{};
  std::int64_t negation_class[hodge_rank]{};
  std::int64_t primitive_class[hodge_rank]{};
  std::int64_t quotient_obstruction[2]{};
  std::int64_t tangent_jet[2]{};
  std::int64_t normal_jet[2]{};
  exact::word identity{};
  exact::word lineage{};
  std::int64_t graph_square{};
  std::int64_t negation_square{};
  std::int64_t mutual_intersection{};
  std::int64_t primitive_square{};
  std::int64_t tangent_obstruction{};
  std::int64_t normal_obstruction{};
  std::uint8_t multiplicity{};
  bool graph_derived{};
  bool diagonal_tangent_exact{};
  bool normal_refused{};
  bool exact{};
};

struct hodge_translation_receipt final {
  parameter_polynomial root{};
  parameter_polynomial other_first{};
  parameter_polynomial other_second{};
  parameter_polynomial kappa{};
  parameter_polynomial x_numerator[2]{};
  parameter_polynomial x_denominator[2]{};
  parameter_polynomial y_scale{};
  std::int64_t graph_class[hodge_rank]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t support{};
  bool identity_map{};
  bool curve_identity{};
  bool involution{};
  bool differential_pullback_identity{};
  bool distinct_support{};
  bool h1_identity{};
  bool exact{};
};

struct hodge_cycle_generator final {
  exact::word identity{};
  exact::word lineage{};
  std::int64_t cycle_class[hodge_rank]{};
  std::uint16_t support_mask{};
  bool effective{};
};

struct hodge_realizer final {
  std::int8_t coefficients[hodge_cycle_generator_capacity]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint16_t support_mask{};
  std::uint8_t denominator{};
  bool effective_single_graph{};
  bool integral{};
  bool exact{};
};

struct hodge_realizer_fiber final {
  hodge_class_question target{};
  hodge_realizer realizers[hodge_realizer_capacity]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint16_t enumerated{};
  std::uint8_t realizer_count{};
  std::uint8_t effective_count{};
  bool integral_member{};
  bool outside_image{};
  bool complete{};
  bool exact{};
};

struct hodge_cycle_receipt final {
  hodge_translation_receipt translations[hodge_translation_capacity]{};
  hodge_cycle_generator generators[hodge_cycle_generator_capacity]{};
  hodge_realizer_fiber fibers[hodge_target_capacity]{};
  hodge_locus_receipt locus{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t generator_count{};
  std::uint8_t image_rank{};
  bool translations_distinct{};
  bool graph_relation_exact{};
  bool rational_integral_separated{};
  bool alternatives_retained{};
  bool exact{};
};

struct hodge_blowup_receipt final {
  std::int64_t pairing[hodge_blowup_rank][hodge_blowup_rank]{};
  std::int64_t pullback[hodge_blowup_rank][hodge_rank]{};
  std::int64_t pushforward[hodge_rank][hodge_blowup_rank]{};
  std::int64_t strict_classes[hodge_translation_capacity][hodge_blowup_rank]{};
  std::int64_t self_intersections[hodge_translation_capacity]{};
  bool through_center[hodge_translation_capacity]{};
  std::int64_t exceptional[hodge_blowup_rank]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t center_selector{};
  std::uint8_t rank{};
  std::uint8_t kernel_rank{};
  bool exceptional_square_minus_one{};
  bool pull_push_identity{};
  bool projection_formula{};
  bool mapping_cone_residual_exact{};
  bool all_push_to_graph{};
  bool exact{};
};

struct hodge_realization_receipt final {
  hodge_realization_card mounted{};
  hodge_realization_question question{};
  hodge_factor_receipt factors[hodge_factor_capacity]{};
  hodge_product_receipt product{};
  hodge_cycle_receipt cycles{};
  hodge_blowup_receipt blowup{};
  hodge_realization_plan theory{};
  hodge_realization_obstruction obstruction{hodge_realization_obstruction::invalid_foundation};
  bool no_expected_invariants{};
  bool alternatives_retained{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
