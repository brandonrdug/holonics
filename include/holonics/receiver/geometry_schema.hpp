#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::receiver {

inline constexpr std::size_t geometry_point_count = 4;
inline constexpr std::size_t sameness_receiver_capacity = 3;
inline constexpr std::size_t projection_source_capacity = 4;
inline constexpr std::size_t connection_edge_capacity = 4;
inline constexpr std::size_t hypergeometric_term_capacity = 4;
inline constexpr std::size_t cube_edge_capacity = 12;

struct word_pair final {
  exact::word first{};
  exact::word second{};
};

struct projective_swing_program final {
  exact::word points[geometry_point_count]{};
  exact::word degenerate_points[geometry_point_count]{};
  exact::word frame[4]{};
  exact::word path{};
  bool field_carrier{};
  bool counterexample_field_carrier{};
};

struct sameness_program final {
  exact::word occurrences[2]{};
  exact::word diagram_incidence[2]{};
  exact::word diagram_marks[2]{};
  exact::word receiver_faces[2][sameness_receiver_capacity]{};
  exact::word receiver_successors[2][sameness_receiver_capacity]{};
  exact::word presentations[2]{};
  exact::word encodings[2]{};
  exact::word collision_encodings[2]{};
  exact::word digest_mask{};
  bool diagram_bijection{};
  bool quasi_inverse{};
  bool unit_witness{};
  bool counit_witness{};
};

struct projection_program final {
  exact::word source_occurrences[projection_source_capacity]{};
  exact::word geometry[projection_source_capacity]{};
  exact::word propagation[projection_source_capacity]{};
  exact::word receiver_masks[2]{};
  exact::word source_incidence{};
  exact::word lineage{};
};

struct connection_program final {
  exact::word initial_fiber{};
  exact::word edge_magnitudes[connection_edge_capacity]{};
  bool edge_negative[connection_edge_capacity]{};
  exact::word start_endpoint{};
  exact::word end_endpoint{};
  exact::word plaquette_boundary_support{};
  exact::word path_support{};
  exact::word open_start{};
  exact::word open_end{};
  exact::word open_path_residual{};
  exact::word lineage{};
};

enum class solution_family : std::uint8_t { gauss, confluent, generalized };

struct hypergeometric_program final {
  exact::word a{};
  exact::word b{};
  exact::word c{};
  word_pair initial_coefficient{};
  exact::word branch{};
  exact::word path{};
  exact::word lineage{};
  exact::word monodromy[4]{};
  solution_family family{solution_family::gauss};
  std::uint16_t term_count{};
};

struct extended_carrier_program final {
  exact::word line_carrier{};
  exact::word sheet_carrier{};
  exact::word higher_carrier{};
  exact::word line_sheet_contact{};
  exact::word sheet_higher_contact{};
  exact::word knot_embedding{};
  exact::word received_diagram{};
  exact::word braid_presentation{};
  exact::word higher_face{};
};

struct information_geometry_program final {
  exact::word delta_time{};
  exact::word delta_space{};
  word_pair metric[2]{};
  word_pair receiver_clocks[2]{};
  exact::word connection_delta{};
  exact::word carried_phase{};
  exact::word first_support{};
  exact::word second_support{};
  exact::word missing_relativistic_obligations{};
  exact::word accelerometer_domain{};
  exact::word cycle_domain{};
};

struct geometry_program final {
  exact::word identity{};
  projective_swing_program swing{};
  sameness_program sameness{};
  projection_program projection{};
  connection_program connection{};
  hypergeometric_program hypergeometric{};
  extended_carrier_program carrier{};
  information_geometry_program information{};
};

}  // namespace holonics::receiver
