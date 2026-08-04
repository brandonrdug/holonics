#pragma once

#include <holonics/organ/phase_crystal_schema.hpp>

namespace holonics::organ {

struct phase_case_receipt final {
  exact::word identity{};
  phase_case_definition definition{};
  std::uint16_t gcd{};
  std::uint16_t lcm{};
  std::uint16_t orbit_count{};
  std::uint16_t orbit_length{};
  std::uint16_t vertex_count{};
  std::uint16_t phase_edge_count{};
  std::uint16_t cell_count{};
  std::uint16_t seam_count{};
  std::uint16_t first_edge_types{};
  std::uint16_t second_edge_types{};
  std::uint16_t cell_shape_types{};
  std::uint16_t shape_transition_types{};
  std::uint16_t largest_shape_population{};
  std::uint16_t largest_transition_population{};
  std::uint16_t hull_corners{};
  std::uint16_t contracted_sides{};
  std::uint16_t hull_edge_types{};
  std::uint16_t series_terms{};
  std::int16_t boundary_residual{};
  phase_ratio first_shortest_side{};
  phase_ratio first_longest_side{};
  phase_ratio second_shortest_side{};
  phase_ratio second_longest_side{};
  phase_ratio receiver_shortest_hull_side{};
  phase_ratio receiver_longest_hull_side{};
  std::uint64_t shape_population_fold{};
  std::uint64_t transition_population_fold{};
  bool exact{};
  bool coprime{};
  bool orbit_partition_exact{};
  bool complete_boundary_cancels{};
  bool cell_population_factorized{};
  bool chronology_distribution_exact{};
  bool hull_exact{};
  bool series_recurrence_exact{};
  bool series_closed_form_detected{};
  bool carrier_coordinate_dimension_four{};
  bool cell_dimension_two{};
  bool receiver_dimension_two{};
  bool screen_crossings_are_contacts{};
};

struct phase_crystal_receipt final {
  phase_crystal_question question{};
  phase_case_receipt cases[phase_crystal_case_capacity]{};
  phase_crystal_theory_plan theory{};
  phase_crystal_obstruction obstruction{phase_crystal_obstruction::invalid_foundation};
  std::uint16_t returned_cases{};
  std::uint16_t prime_cases{};
  std::uint16_t composite_cases{};
  std::uint16_t shared_factor_cases{};
  std::uint16_t control_cases{};
  std::uint16_t total_shape_types{};
  std::uint16_t total_transition_types{};
  bool all_intrinsic_cells_exact{};
  bool all_series_exact{};
  bool dilation_control_exact{};
  bool turn_control_exact{};
  bool reversal_control_exact{};
  bool mode_field_absent{};
  bool expected_shape_absent{};
  bool historical_renderer_absent{};
  bool theory_formed{};
};

}  // namespace holonics::organ
