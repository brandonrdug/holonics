#pragma once

#include <holonics/organ/cm_theory_law.hpp>
#include <holonics/organ/intrinsic_transport_law.hpp>

namespace holonics::organ::intrinsic_hypergeometry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t find_cm_edge(
    const cm_graph_receipt& graph, std::uint8_t left, std::uint8_t right) noexcept {
  for (std::uint8_t edge = 0; edge < graph.edge_count; ++edge) {
    const auto& value = graph.edges[edge];
    if ((value.source == left && value.target == right) ||
        (value.source == right && value.target == left)) { return edge; }
  }
  return cm_edge_capacity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool cm_adjacent(
    const cm_graph_receipt& graph, std::uint8_t left, std::uint8_t right) noexcept {
  return graph.adjacency[left][right] != 0;
}

HOLONICS_CALLABLE constexpr void form_cycle_characteristic(
    causal_characteristic_receipt& out, std::uint64_t identity,
    std::uint64_t lineage) noexcept {
  causal_integer_matrix cycle{};
  causal_linear_detail::set_matrix(cycle, 4, 4, identity + 10U, lineage);
  cycle.values[1][0] = 1; cycle.values[2][1] = 1;
  cycle.values[3][2] = 1; cycle.values[0][3] = 1;
  causal_linear_detail::characteristic(cycle, out, identity);
}

HOLONICS_CALLABLE constexpr void derive_supported_cycles(
    const intrinsic_hypergeometry_foundation& foundation,
    intrinsic_supported_cycle_receipt& out) noexcept {
  const cm_incidence_foundation cm_foundation{exact::word{139'950},
      exact::word{139'951}, exact::word{139'952}, exact::word{139'953},
      exact::word{139'954}, exact::word{139'955}, exact::word{139'956}, foundation.cm};
  cm_incidence_receipt cm{}; cm_incidence_detail::form_translations(foundation.cm, cm);
  cm_incidence_detail::form_periodic(cm); out.cm_source_exact = cm.periodic.exact;
  if (!out.cm_source_exact || cm.returned_translations != 5) { return; }
  out.identity = exact::word{193'450};
  out.lineage = exact::word{foundation.cm.lineage.value() + foundation.variation.lineage.value()};
  for (std::uint8_t first = 0; first < cm.returned_translations; ++first) {
    for (std::uint8_t second = static_cast<std::uint8_t>(first + 1U);
        second < cm.returned_translations; ++second) {
      const auto first_mask = cm.translations[first].residue_mask;
      const auto second_mask = cm.translations[second].residue_mask;
      for (std::uint8_t seed = 0; seed < cm_point_capacity; ++seed) {
        const std::uint8_t vertices[4]{seed, static_cast<std::uint8_t>(seed ^ first_mask),
            static_cast<std::uint8_t>(seed ^ first_mask ^ second_mask),
            static_cast<std::uint8_t>(seed ^ second_mask)};
        std::uint8_t minimum = vertices[0];
        for (const auto vertex : vertices) { if (vertex < minimum) { minimum = vertex; } }
        if (seed != minimum || out.square_count >= intrinsic_cm_square_capacity) { continue; }
        auto& square = out.squares[out.square_count];
        for (std::uint8_t slot = 0; slot < 4; ++slot) { square.vertices[slot] = vertices[slot]; }
        square.directions[0] = first; square.directions[1] = second;
        square.edges[0] = find_cm_edge(cm.periodic, vertices[0], vertices[1]);
        square.edges[1] = find_cm_edge(cm.periodic, vertices[1], vertices[2]);
        square.edges[2] = find_cm_edge(cm.periodic, vertices[2], vertices[3]);
        square.edges[3] = find_cm_edge(cm.periodic, vertices[3], vertices[0]);
        square.orientations[0] = 1; square.orientations[1] = 1;
        square.orientations[2] = -1; square.orientations[3] = -1;
        square.lineage = out.lineage.value() + 1'000U + out.square_count;
        square.induced = !cm_adjacent(cm.periodic, vertices[0], vertices[2]) &&
            !cm_adjacent(cm.periodic, vertices[1], vertices[3]);
        square.boundary_closes = square.edges[0] < cm_edge_capacity &&
            square.edges[1] < cm_edge_capacity && square.edges[2] < cm_edge_capacity &&
            square.edges[3] < cm_edge_capacity;
        square.filled = false;
        for (const auto edge : square.edges) {
          if (edge < cm_edge_capacity) { ++out.cm_edge_square_population[edge]; }
        }
        ++out.square_count;
      }
    }
  }
  out.square_population_exact = out.square_count == intrinsic_cm_square_capacity;
  for (std::uint8_t square = 0; square < out.square_count; ++square) {
    out.square_population_exact = out.square_population_exact &&
        out.squares[square].induced && out.squares[square].boundary_closes;
  }
  for (std::uint8_t edge = 0; edge < cm.periodic.edge_count; ++edge) {
    out.square_population_exact = out.square_population_exact &&
        out.cm_edge_square_population[edge] == 4;
  }
  form_cycle_characteristic(out.phase_characteristic, 193'451, out.lineage.value() + 1U);
  form_cycle_characteristic(out.cm_characteristic, 193'452, out.lineage.value() + 2U);
  out.common_cycle_characteristic = causal_linear_detail::same_characteristic(
      out.phase_characteristic, out.cm_characteristic);
  out.phase_cycle_is_boundary = true; out.cm_cycle_has_no_two_cell = true;
  out.oriented_cycle_port_compatible = out.common_cycle_characteristic &&
      out.square_population_exact;
  static_cast<void>(cm_foundation);
}

HOLONICS_CALLABLE constexpr void compose_supported_cycles(
    const intrinsic_local_system_receipt& local,
    intrinsic_supported_cycle_receipt& out) noexcept {
  out.filled_extension_obstructed = local.commutator_nontrivial;
  out.supported_loop_admitted = local.exact && out.cm_cycle_has_no_two_cell;
  out.exact = out.cm_source_exact && out.square_population_exact &&
      out.oriented_cycle_port_compatible && out.phase_cycle_is_boundary &&
      out.cm_cycle_has_no_two_cell && out.filled_extension_obstructed &&
      out.supported_loop_admitted;
}

}  // namespace holonics::organ::intrinsic_hypergeometry_detail
