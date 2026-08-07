#include "r2_cases.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

[[nodiscard]] structure::structure_case base_case(std::size_t slot) {
  structure::structure_case input{};
  input.case_identity = 8'192U + static_cast<std::uint64_t>(slot);
  input.owner_seed = 10'000U + static_cast<std::uint64_t>(slot) * 100U;
  return input;
}

std::uint16_t add_cell(
    structure::structure_case& input,
    std::uint8_t dimension,
    std::uint64_t multiplicity = 1) {
  const std::uint16_t slot = input.cell_count;
  input.cells[slot] = structure::encoded_cell{dimension, multiplicity};
  ++input.cell_count;
  return slot;
}

void add_incidence(
    structure::structure_case& input,
    std::uint16_t higher,
    std::uint16_t lower,
    std::int8_t orientation,
    std::uint64_t multiplicity = 1) {
  input.incidences[input.incidence_count] =
      structure::encoded_incidence{higher, lower, orientation, multiplicity};
  ++input.incidence_count;
}

std::uint16_t add_triangle(
    structure::structure_case& input,
    std::uint64_t edge_multiplicity,
    std::uint64_t face_multiplicity) {
  const auto v0 = add_cell(input, 0);
  const auto v1 = add_cell(input, 0);
  const auto v2 = add_cell(input, 0);
  const auto e01 = add_cell(input, 1);
  const auto e12 = add_cell(input, 1);
  const auto e02 = add_cell(input, 1);
  const auto face = add_cell(input, 2);
  add_incidence(input, e01, v0, -1, edge_multiplicity);
  add_incidence(input, e01, v1, 1, edge_multiplicity);
  add_incidence(input, e12, v1, -1, edge_multiplicity);
  add_incidence(input, e12, v2, 1, edge_multiplicity);
  add_incidence(input, e02, v0, -1, edge_multiplicity);
  add_incidence(input, e02, v2, 1, edge_multiplicity);
  add_incidence(input, face, e01, 1, face_multiplicity);
  add_incidence(input, face, e12, 1, face_multiplicity);
  add_incidence(input, face, e02, -1, face_multiplicity);
  return face;
}

void set_tetrahedron(structure::structure_case& input) {
  for (std::size_t slot = 0; slot < 4; ++slot) {
    static_cast<void>(add_cell(input, 0));
  }
  const auto e01 = add_cell(input, 1);
  const auto e02 = add_cell(input, 1);
  const auto e03 = add_cell(input, 1);
  const auto e12 = add_cell(input, 1);
  const auto e13 = add_cell(input, 1);
  const auto e23 = add_cell(input, 1);
  const auto f012 = add_cell(input, 2);
  const auto f013 = add_cell(input, 2);
  const auto f023 = add_cell(input, 2);
  const auto f123 = add_cell(input, 2);
  const auto body = add_cell(input, 3);
  const std::uint16_t edges[6]{e01, e02, e03, e12, e13, e23};
  const std::uint16_t edge_vertices[6][2]{{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
  for (std::size_t edge = 0; edge < 6; ++edge) {
    add_incidence(input, edges[edge], edge_vertices[edge][0], -1);
    add_incidence(input, edges[edge], edge_vertices[edge][1], 1);
  }
  add_incidence(input, f012, e01, 1); add_incidence(input, f012, e02, -1);
  add_incidence(input, f012, e12, 1);
  add_incidence(input, f013, e01, 1); add_incidence(input, f013, e03, -1);
  add_incidence(input, f013, e13, 1);
  add_incidence(input, f023, e02, 1); add_incidence(input, f023, e03, -1);
  add_incidence(input, f023, e23, 1);
  add_incidence(input, f123, e12, 1); add_incidence(input, f123, e13, -1);
  add_incidence(input, f123, e23, 1);
  add_incidence(input, body, f012, -1); add_incidence(input, body, f013, 1);
  add_incidence(input, body, f023, -1); add_incidence(input, body, f123, 1);
  input.traversal_seed = body;
}

}  // namespace

r2_input_batch r2_cases() {
  r2_input_batch cases{};
  for (std::size_t slot = 0; slot < cases.size(); ++slot) {
    cases[slot] = base_case(slot);
  }
  cases[1].traversal_seed = add_cell(cases[1], 0);
  cases[1].append_isolated_count = 1;
  const auto v0 = add_cell(cases[2], 0);
  const auto v1 = add_cell(cases[2], 0);
  const auto edge = add_cell(cases[2], 1);
  add_incidence(cases[2], edge, v0, -1); add_incidence(cases[2], edge, v1, 1);
  cases[2].traversal_seed = edge;
  cases[3].traversal_seed = add_triangle(cases[3], 1, 1);
  cases[4].traversal_seed = add_triangle(cases[4], 1, 1);
  const auto separate_v0 = add_cell(cases[4], 0);
  const auto separate_v1 = add_cell(cases[4], 0);
  const auto separate_edge = add_cell(cases[4], 1);
  add_incidence(cases[4], separate_edge, separate_v0, -1);
  add_incidence(cases[4], separate_edge, separate_v1, 1);
  cases[4].departure_slot = add_cell(cases[4], 0);
  set_tetrahedron(cases[5]);
  cases[6].traversal_seed = add_triangle(cases[6], 2, 3);
  for (std::size_t slot = 0; slot < 15; ++slot) {
    static_cast<void>(add_cell(cases[7], 0));
  }
  cases[7].traversal_seed = 0;
  cases[7].append_isolated_count = 2;
  for (std::size_t slot = 0; slot < 17; ++slot) {
    static_cast<void>(add_cell(cases[8], 0));
  }
  const auto blocked_v0 = add_cell(cases[9], 0);
  const auto blocked_v1 = add_cell(cases[9], 0);
  const auto blocked_edge = add_cell(cases[9], 1);
  add_incidence(cases[9], blocked_edge, blocked_v0, -1);
  add_incidence(cases[9], blocked_edge, blocked_v1, 1);
  cases[9].traversal_seed = blocked_edge;
  cases[9].departure_slot = blocked_v0;
  return cases;
}

}  // namespace holonics::tests
