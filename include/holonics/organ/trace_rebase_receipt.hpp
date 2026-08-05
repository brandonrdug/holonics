#pragma once

#include <holonics/organ/trace_rebase_schema.hpp>

namespace holonics::organ {

struct trace_rebase_state final {
  exact_matrix2 matrices[3]{};
  std::int64_t coordinates[trace_rebase_coordinate_count]{};
  trace_rebase_move path[trace_rebase_path_depth]{};
  exact::word lineage{};
  std::uint16_t ordinal{};
  std::uint8_t source{};
  std::uint8_t seed{};
  std::uint8_t depth{};
  bool branch{};
  bool valid{};
};
struct trace_rebase_edge final {
  exact_matrix2 target_matrices[3]{};
  std::int64_t target[trace_rebase_coordinate_count]{};
  std::int64_t jacobian[trace_rebase_coordinate_count]
                       [trace_rebase_coordinate_count]{};
  std::int64_t source_gradient[trace_rebase_coordinate_count]{};
  std::int64_t target_gradient[trace_rebase_coordinate_count]{};
  std::int64_t tangent[trace_rebase_tangent_rank]
                      [trace_rebase_coordinate_count]{};
  std::int64_t transported[trace_rebase_tangent_rank]
                          [trace_rebase_coordinate_count]{};
  std::uint16_t state{};
  trace_rebase_move move{trace_rebase_move::swap12};
  std::uint8_t source_tangent_rank{};
  std::uint8_t target_tangent_rank{};
  std::uint8_t transported_rank{};
  std::uint8_t source_vertical_rank{};
  std::uint8_t target_vertical_rank{};
  trace_rebase_obstruction differential_obstruction{
      trace_rebase_obstruction::none};
  bool source_branch{};
  bool target_branch{};
  bool chain_exact{};
  bool valid{};
};
struct trace_rebase_candidate final {
  std::int64_t coefficients[trace_rebase_feature_count]{};
  std::uint16_t rows{};
  std::uint8_t degree{};
  std::uint8_t features{};
  std::uint8_t rank{};
  std::uint8_t nullity{};
  trace_rebase_move move{trace_rebase_move::swap12};
  std::uint8_t target{};
  trace_rebase_obstruction obstruction{trace_rebase_obstruction::insufficient_rows};
  bool primitive{};
  bool selected{};
};
struct trace_rebase_map_organ final {
  std::int64_t coefficients[trace_rebase_coordinate_count]
                           [trace_rebase_feature_count]{};
  std::uint8_t degrees[trace_rebase_coordinate_count]{};
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  trace_rebase_move move{trace_rebase_move::swap12};
  bool primitive{};
  bool checker_founded{};
};
struct trace_rebase_witness final {
  std::uint16_t first{};
  std::uint16_t second{};
  std::int64_t vector[trace_rebase_coordinate_count]{};
  std::int64_t image[trace_rebase_coordinate_count]{};
  std::int64_t eigenvalue{};
  std::uint8_t kind{};
  bool found{};
};
struct trace_rebase_counts final {
  std::uint16_t regular_regular{};
  std::uint16_t regular_branch{};
  std::uint16_t branch_regular{};
  std::uint16_t branch_branch{};
};
struct trace_rebase_discovery_receipt final {
  trace_rebase_state states[trace_rebase_state_capacity]{};
  trace_rebase_edge edges[trace_rebase_edge_capacity]{};
  trace_rebase_candidate candidates[trace_rebase_map_count]{};
  trace_rebase_map_organ maps[trace_rebase_move_count]{};
  trace_rebase_witness witnesses[trace_rebase_witness_count]{};
  trace_rebase_counts transitions[trace_rebase_move_count]{};
  trace_rebase_counts source_transitions[trace_rebase_move_count]
                                        [trace_rebase_source_count]{};
  std::uint16_t source_holdout_residuals[trace_rebase_move_count]
                                         [trace_rebase_source_count]{};
  std::uint8_t source_holdout_ranks[trace_rebase_source_count][4]{};
  std::uint8_t coordinate_deleted_rank[trace_rebase_coordinate_count]{};
  std::uint8_t coordinate_deleted_features[trace_rebase_coordinate_count]{};
  std::uint8_t target_deleted_rank{};
  std::uint8_t row_deficient_rank{};
  std::uint8_t degree_two_rank{};
  std::uint8_t control_move{};
  std::uint8_t control_target{};
  std::uint16_t coefficient_height{};
  std::uint16_t coefficient_height_limit{};
  trace_rebase_obstruction degree_two_obstruction{
      trace_rebase_obstruction::insufficient_rows};
  std::uint16_t state_count{};
  std::uint16_t edge_count{};
  std::uint16_t residuals{};
  std::uint16_t tangent_failures{};
  std::uint16_t singular_edges{};
  exact::word passage{};
  exact::word lineage{};
  bool source_ports_distinct{};
  bool population_complete{};
  bool controls_complete{};
  bool witnesses_complete{};
  bool theory_formed{};
};
struct trace_rebase_basis final {
  std::int64_t rows[trace_rebase_feature_count]
                   [trace_rebase_joint_column_count]{};
  std::uint8_t pivots[trace_rebase_feature_count]{};
  std::uint8_t rank{};
  bool exact{true};
};
struct trace_rebase_workspace final { trace_rebase_basis basis{}; };

struct heldout_trace_rebase_source final {
  exact_matrix2 matrices[trace_rebase_heldout_path_capacity + 1U][3]{};
  std::int64_t coordinates[trace_rebase_heldout_path_capacity + 1U]
                          [trace_rebase_coordinate_count]{};
  exact::word lineage{};
  std::uint8_t path_length{};
  bool valid{};
};
struct heldout_trace_rebase_receipt final {
  std::int64_t predicted[trace_rebase_heldout_path_capacity + 1U]
                        [trace_rebase_coordinate_count]{};
  std::int64_t source[trace_rebase_heldout_path_capacity + 1U]
                     [trace_rebase_coordinate_count]{};
  std::uint8_t tangent_rank[trace_rebase_heldout_path_capacity + 1U]{};
  std::uint8_t vertical_rank[trace_rebase_heldout_path_capacity + 1U]{};
  std::uint8_t transported_rank[trace_rebase_heldout_path_capacity]{};
  bool branch[trace_rebase_heldout_path_capacity + 1U]{};
  bool transport_exact[trace_rebase_heldout_path_capacity]{};
  trace_rebase_obstruction step_obstruction[
      trace_rebase_heldout_path_capacity]{};
  trace_rebase_move moves[trace_rebase_heldout_path_capacity]{};
  trace_rebase_obstruction map_exclusion{};
  trace_rebase_obstruction lift_exclusion{};
  trace_rebase_obstruction orientation_exclusion{};
  trace_rebase_obstruction aperture_control{};
  trace_rebase_obstruction determinant_control{};
  exact::word passage{};
  exact::word lineage{};
  std::uint8_t path_length{};
  std::uint16_t residuals{};
  bool prediction_before_comparison{};
  bool compared{};
  bool source_detached{};
  bool theory_formed{};
};

} // namespace holonics::organ
