#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/geometry_receipt.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr extended_carrier_receipt weave_extended_carriers(
    const extended_carrier_program& program,
    bool interchange_certified) noexcept {
  extended_carrier_receipt result{};
  result.carriers[0] = program.line_carrier;
  result.carriers[1] = program.sheet_carrier;
  result.carriers[2] = program.higher_carrier;
  result.contacts[0] = program.line_sheet_contact;
  result.contacts[1] = program.sheet_higher_contact;
  result.knot_embedding = program.knot_embedding;
  result.received_diagram = program.received_diagram;
  result.braid_presentation = program.braid_presentation;
  result.higher_face = program.higher_face;
  result.line_boundary_count = 2;
  const std::uint8_t sheet_edges[4][2]{{0, 1}, {1, 2}, {2, 3}, {3, 0}};
  for (std::size_t edge = 0; edge < 4; ++edge) {
    --result.sheet_vertex_residuals[sheet_edges[edge][0]];
    ++result.sheet_vertex_residuals[sheet_edges[edge][1]];
  }
  result.sheet_boundary_squared_zero = true;
  for (std::size_t vertex = 0; vertex < 4; ++vertex) {
    result.sheet_boundary_squared_zero &= result.sheet_vertex_residuals[vertex] == 0;
  }
  const std::uint8_t face_edges[6][4]{
      {0, 1, 2, 3}, {4, 5, 6, 7}, {0, 4, 8, 9},
      {2, 6, 10, 11}, {3, 7, 8, 11}, {1, 5, 9, 10}};
  const bool face_negative[6][4]{
      {false, false, true, true}, {true, true, false, false},
      {true, false, false, true}, {false, true, false, true},
      {false, true, true, false}, {true, false, false, true}};
  for (std::size_t face = 0; face < 6; ++face) {
    for (std::size_t edge = 0; edge < 4; ++edge) {
      const std::size_t slot = face_edges[face][edge];
      const int contribution = face_negative[face][edge] ? -1 : 1;
      result.higher_edge_residuals[slot] = static_cast<std::int8_t>(
          static_cast<int>(result.higher_edge_residuals[slot]) + contribution);
    }
  }
  result.higher_boundary_squared_zero = true;
  for (std::size_t edge = 0; edge < cube_edge_capacity; ++edge) {
    result.higher_boundary_squared_zero &= result.higher_edge_residuals[edge] == 0;
  }
  result.contacts_typed = program.line_sheet_contact.value() != 0 &&
      program.sheet_higher_contact.value() != 0 &&
      program.line_sheet_contact != program.sheet_higher_contact;
  result.presentations_distinct = program.knot_embedding != program.received_diagram &&
      program.knot_embedding != program.braid_presentation &&
      program.received_diagram != program.braid_presentation &&
      program.higher_face != program.knot_embedding;
  result.braid_interchange_certified = interchange_certified;
  return result;
}

}  // namespace holonics::receiver
