#pragma once

#include <holonics/organ/intrinsic_hypergeometry_schema.hpp>
#include <holonics/organ/phase_crystal_geometry.hpp>

namespace holonics::organ {

struct intrinsic_vertex_receipt final {
  phase_ratio factor_coordinates[4]{};
  phase_crystal_detail::phase_point projected{};
  std::uint16_t star_edges[4]{};
  std::uint16_t star_faces[4]{};
  std::uint16_t link_vertices[4]{};
  std::uint32_t section_after[4]{};
  std::uint64_t lineage{};
  std::uint16_t successor{};
  std::uint16_t projection_fiber{};
  std::uint16_t tour_position{};
  std::uint8_t tour{};
  intrinsic_seam seam{intrinsic_seam::interior};
};

struct intrinsic_edge_receipt final {
  std::uint64_t lineage{};
  std::uint16_t source{};
  std::uint16_t target{};
  std::uint16_t incident_faces[2]{};
  std::int8_t incident_orientation[2]{};
  std::uint8_t axis{};
  bool wraps{};
};

struct intrinsic_face_receipt final {
  std::uint64_t lineage{};
  std::uint16_t vertices[4]{};
  std::uint16_t edges[4]{};
  std::int8_t orientations[4]{};
  bool boundary_closes{};
  bool filled{};
};

struct intrinsic_flag_receipt final {
  std::uint64_t lineage{};
  std::uint16_t vertex{};
  std::uint16_t edge{};
  std::uint16_t face{};
  std::int8_t orientation{};
};

struct intrinsic_tour_receipt final {
  std::uint32_t return_matrix[4]{};
  std::uint64_t word_fold{};
  std::uint16_t first_vertex{};
  std::uint16_t length{};
  bool determinant_one{};
};

struct intrinsic_phase_case_receipt final {
  intrinsic_vertex_receipt vertices[intrinsic_vertex_capacity]{};
  intrinsic_edge_receipt edges[intrinsic_edge_capacity]{};
  intrinsic_face_receipt faces[intrinsic_face_capacity]{};
  intrinsic_flag_receipt flags[intrinsic_flag_capacity]{};
  intrinsic_tour_receipt tours[intrinsic_tour_capacity]{};
  std::uint32_t transition_population[4][4]{};
  std::uint32_t face_intersections[5][5]{};
  std::uint16_t projection_fiber_sizes[intrinsic_vertex_capacity]{};
  std::uint16_t seam_receiver_fibers[4]{};
  exact::word identity{};
  exact::word lineage{};
  intrinsic_presentation presentation{};
  std::uint16_t gcd{};
  std::uint16_t lcm{};
  std::uint16_t vertex_count{};
  std::uint16_t edge_count{};
  std::uint16_t face_count{};
  std::uint16_t flag_count{};
  std::uint16_t projection_fiber_count{};
  std::uint16_t recurrence_depth{};
  std::uint8_t tour_count{};
  std::uint8_t seam_receiver_hull_corners{};
  bool coordinates_exact{};
  bool incidence_exact{};
  bool stars_links_exact{};
  bool boundaries_exact{};
  bool seams_shared_exact{};
  bool chronology_exact{};
  bool projection_fibers_complete{};
  bool distributions_exact{};
  bool sections_exact{};
  bool exact{};
};

}  // namespace holonics::organ
