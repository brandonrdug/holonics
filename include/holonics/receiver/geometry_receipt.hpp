#pragma once

#include <cstdint>

#include <holonics/receiver/geometry_schema.hpp>

namespace holonics::receiver {

enum class geometry_obstruction : std::uint8_t {
  none,
  invalid_program,
  degenerate_swing,
  non_field_carrier,
  open_global_geometry
};

struct projective_swing_receipt final {
  word_pair original{};
  word_pair transformed{};
  exact::word path{};
  geometry_obstruction obstruction{geometry_obstruction::none};
  bool projectively_equal{};
  bool frame_changed{};
  bool degenerate_open{};
  bool non_field_open{};
};

struct sameness_receipt final {
  bool occurrence_equal{};
  bool marked_diagram_isomorphic{};
  bool doctrinal_equivalent{};
  bool observationally_equivalent{};
  bool receiver_face_equal{};
  bool presentation_equal{};
  bool byte_equal{};
  bool digest_equal{};
  bool equal_face_distinct_occurrence{};
  bool equal_bytes_distinct_soul{};
  bool digest_collision_retained{};
  bool byte_implies_digest{};
};

struct projection_receipt final {
  exact::word faces[2]{};
  exact::word preimage_supports[2]{};
  exact::word preimage_occurrences[2][projection_source_capacity]{};
  exact::word source_incidence_before{};
  exact::word source_incidence_after{};
  exact::word created_source_incidence{};
  exact::word lineage{};
  std::uint16_t preimage_counts[2]{};
  bool unresolved_preimage{};
  bool counterexample_receivers_differ{};
};

struct signed_word final {
  exact::word magnitude{};
  bool negative{};
};

struct connection_receipt final {
  exact::word start_endpoint{};
  exact::word end_endpoint{};
  exact::word initial_fiber{};
  exact::word transported_fiber{};
  signed_word finite_holonomy{};
  signed_word local_curvature{};
  exact::word lineage{};
  bool endpoint_equal{};
  bool curvature_certified{};
  bool open_path_residual_is_holonomy{};
  bool global_triviality_open{};
};

struct hypergeometric_receipt final {
  exact::word parameters[3]{};
  exact::word singular_locus[3]{};
  word_pair coefficients[hypergeometric_term_capacity]{};
  exact::word branch{};
  exact::word path{};
  exact::word lineage{};
  exact::word monodromy[4]{};
  solution_family family{solution_family::gauss};
  std::uint16_t term_count{};
  bool recurrence_exact{};
  bool singular_locus_retained{};
  bool branch_retained{};
  bool confluent_distinct{};
  bool generalized_distinct{};
};

struct extended_carrier_receipt final {
  exact::word carriers[3]{};
  exact::word contacts[2]{};
  exact::word knot_embedding{};
  exact::word received_diagram{};
  exact::word braid_presentation{};
  exact::word higher_face{};
  std::int8_t sheet_vertex_residuals[4]{};
  std::int8_t higher_edge_residuals[cube_edge_capacity]{};
  std::uint16_t line_boundary_count{};
  bool sheet_boundary_squared_zero{};
  bool higher_boundary_squared_zero{};
  bool contacts_typed{};
  bool presentations_distinct{};
  bool braid_interchange_certified{};
  bool literal_physical_identity{};
};

struct information_geometry_receipt final {
  exact::word interval_magnitude{};
  exact::word interval_denominator{};
  word_pair metric[2]{};
  word_pair receiver_clocks[2]{};
  exact::word current_before{};
  exact::word current_after{};
  exact::word carried_phase{};
  exact::word returned_stress{};
  exact::word first_support{};
  exact::word second_support{};
  exact::word standing_head{};
  exact::word missing_relativistic_obligations{};
  bool interval_negative{};
  bool causal_accessible{};
  bool metric_declared{};
  bool receiver_clocks_distinct{};
  bool connection_declared{};
  bool repeated_support{};
  bool complete_state_recurrence{};
  bool accelerometer_domain_relative{};
  bool cycle_domain_relative{};
  bool general_relativistic_fidelity{};
};

struct geometry_observation final {
  exact::word program_identity{};
  projective_swing_receipt swing{};
  sameness_receipt sameness{};
  projection_receipt projection{};
  connection_receipt connection{};
  hypergeometric_receipt hypergeometric{};
  extended_carrier_receipt carrier{};
  information_geometry_receipt information{};
  geometry_obstruction obstruction{geometry_obstruction::none};
  bool all_deeds_returned{};
};

}  // namespace holonics::receiver
