#pragma once

#include <holonics/organ/characteristic_hypergeometry_schema.hpp>

namespace holonics::organ {

enum class hypergeometry_trace_obstruction : std::uint8_t {
  none,
  insufficient_rows,
  full_rank,
  nonunique_kernel,
  residual,
  witness_absent,
  organ_absent,
  unsupported_determinant,
  comparison_residual
};

struct characteristic_pair_receipt final {
  exact_matrix2 first{};
  exact_matrix2 second{};
  exact_matrix2 product{};
  exact_matrix2 closed{};
  std::int64_t trace_first{};
  std::int64_t trace_second{};
  std::int64_t trace_product{};
  std::int64_t trace_closed{};
  std::int64_t discriminants[4]{};
  std::uint16_t left_word{};
  std::uint16_t right_word{};
  std::uint8_t source{};
  std::uint8_t fixed_ranks[4]{};
  std::int8_t strata[4]{};
  bool valid{};
};

struct characteristic_group_receipt final {
  std::int64_t coordinates[4]{};
  std::int8_t strata[4]{};
  std::uint16_t population{};
  std::uint8_t closed_fixed_rank{};
  bool valid{};
};

struct trace_law_candidate_receipt final {
  std::int64_t coefficients[characteristic_feature_count]{};
  std::uint16_t rows{};
  std::uint8_t features{};
  std::uint8_t rank{};
  std::uint8_t nullity{};
  hypergeometry_trace_obstruction obstruction{
      hypergeometry_trace_obstruction::insufficient_rows};
  bool primitive{};
  bool selected{};
};

struct characteristic_collision_receipt final {
  std::uint16_t first_pair{};
  std::uint16_t second_pair{};
  std::uint8_t kind{};
  bool found{};
};

struct trace_law_organ final {
  std::int64_t coefficients[characteristic_feature_count]{};
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  std::uint8_t features{};
  bool primitive{};
  bool checker_founded{};
};

struct characteristic_hypergeometry_receipt final {
  transition_word_population words[characteristic_source_count]{};
  characteristic_pair_receipt pairs[characteristic_pair_capacity]{};
  characteristic_group_receipt groups[characteristic_group_capacity]{};
  trace_law_candidate_receipt candidates[characteristic_candidate_count]{};
  characteristic_collision_receipt witnesses[characteristic_witness_count]{};
  trace_law_organ organ{};
  std::uint16_t pair_count[characteristic_source_count]{};
  std::uint16_t group_count{};
  std::uint16_t closed_strata[3]{};
  std::uint16_t law_residuals{};
  exact::word passage{};
  exact::word lineage{};
  bool development_ports_distinct{};
  bool census_complete{};
  bool witnesses_complete{};
  bool theory_formed{};
};

struct heldout_characteristic_receipt final {
  exact_matrix2 first{};
  exact_matrix2 second{};
  exact_matrix2 product{};
  exact_matrix2 closed{};
  std::int64_t visible[3]{};
  std::int64_t predicted_trace{};
  std::int64_t source_trace{};
  std::int64_t predicted_discriminant{};
  std::int64_t characteristic[3]{};
  std::uint8_t predicted_fixed_rank{};
  hypergeometry_trace_obstruction exclusion{
      hypergeometry_trace_obstruction::none};
  hypergeometry_trace_obstruction changed{
      hypergeometry_trace_obstruction::none};
  exact::word passage{};
  exact::word lineage{};
  bool development_sources_absent{};
  bool prediction_before_comparison{};
  bool ablation_exact{};
  bool improved{};
  bool theory_formed{};
};

struct trace_basis final {
  exact::small_rational rows[characteristic_feature_count]
                            [characteristic_feature_count]{};
  std::uint8_t pivots[characteristic_feature_count]{};
  std::uint8_t rank{};
};

struct characteristic_workspace final {
  trace_basis bases[4]{};
};

} // namespace holonics::organ
