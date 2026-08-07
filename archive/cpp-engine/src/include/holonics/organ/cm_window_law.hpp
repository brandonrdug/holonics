#pragma once

#include <holonics/organ/cm_incidence_law.hpp>

namespace holonics::organ::cm_window_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool bounded_vertex(const cm_element& value,
    const cm_problem_card& card, std::uint8_t& vertex) noexcept {
  vertex = 0;
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    if (value.coefficients[slot] < card.window_min ||
        value.coefficients[slot] > card.window_max) { return false; }
    if (value.coefficients[slot] == card.window_max) {
      vertex = static_cast<std::uint8_t>(vertex | (1U << slot));
    }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void form_window(cm_incidence_receipt& out) noexcept {
  auto& graph = out.window;
  auto& projection = out.projection;
  graph.identity = exact::word{190'430};
  graph.lineage = out.mounted.lineage.value() + graph.identity.value();
  projection.identity = exact::word{190'440};
  projection.lineage = out.mounted.lineage.value() + projection.identity.value();
  bool arithmetic_exact = true;
  for (std::uint8_t vertex = 0; vertex < cm_point_capacity; ++vertex) {
    projection.points[vertex] = cm_arithmetic_detail::point(vertex);
  }
  for (std::uint8_t source = 0; source < cm_point_capacity; ++source) {
    for (std::uint8_t direction = 0; direction < out.returned_translations; ++direction) {
      const auto translated = cm_arithmetic_detail::add(projection.points[source],
          out.translations[direction].value, arithmetic_exact);
      std::uint8_t target = 0;
      if (bounded_vertex(translated, out.mounted, target)) {
        graph.adjacency[source][target] = 1;
        graph.adjacency[target][source] = 1;
      }
    }
  }
  for (std::uint8_t source = 0; source < cm_point_capacity; ++source) {
    for (std::uint8_t target = static_cast<std::uint8_t>(source + 1U);
        target < cm_point_capacity; ++target) {
      if (graph.adjacency[source][target] == 0) { continue; }
      bool exact = true;
      const auto difference = cm_arithmetic_detail::subtract(
          projection.points[target], projection.points[source], exact);
      const auto direction = cm_incidence_detail::direction_of(difference, out);
      arithmetic_exact = arithmetic_exact && exact && direction < out.returned_translations;
      cm_incidence_detail::append_edge(graph, source, target, direction,
          out.translations[direction].lineage);
    }
  }
  graph.symmetric = true;
  for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
    for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
      graph.degree[row] = static_cast<std::uint8_t>(
          graph.degree[row] + graph.adjacency[row][column]);
      graph.symmetric = graph.symmetric &&
          graph.adjacency[row][column] == graph.adjacency[column][row];
    }
  }
  graph.exact = arithmetic_exact && graph.symmetric;
}

HOLONICS_CALLABLE constexpr void form_expanded_projection(cm_incidence_receipt& out) noexcept {
  auto& projection = out.projection;
  bool exact = true;
  projection.basis_injective = true;
  for (std::uint8_t left = 0; left < cm_point_capacity; ++left) {
    for (std::uint8_t right = static_cast<std::uint8_t>(left + 1U);
        right < cm_point_capacity; ++right) {
      projection.basis_injective = projection.basis_injective &&
          !cm_arithmetic_detail::equal(projection.points[left], projection.points[right]);
      bool pair_exact = true;
      const auto difference = cm_arithmetic_detail::subtract(
          projection.points[right], projection.points[left], pair_exact);
      const auto pair_norm = cm_arithmetic_detail::norm(difference, pair_exact);
      if (cm_arithmetic_detail::equal(pair_norm, cm_arithmetic_detail::one())) {
        const auto direction = cm_incidence_detail::direction_of(difference, out);
        pair_exact = pair_exact && direction < out.returned_translations;
        if (direction < out.returned_translations) {
          projection.expanded_adjacency[left][right] = 1;
          projection.expanded_adjacency[right][left] = 1;
          ++projection.direction_population[direction];
          ++projection.unit_pair_count;
        }
      }
      exact = exact && pair_exact;
    }
  }
  projection.factor_expansion_agree = true;
  for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
    for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
      const bool same = projection.expanded_adjacency[row][column] ==
          out.window.adjacency[row][column];
      projection.factor_expansion_agree = projection.factor_expansion_agree && same;
      if (!same) { ++projection.projection_loss; }
    }
  }
  for (std::uint8_t edge = 0; edge < out.periodic.edge_count; ++edge) {
    const auto& source = out.periodic.edges[edge];
    if (out.window.adjacency[source.source][source.target] != 0) { continue; }
    auto& lost = projection.lost[projection.lost_count++];
    lost = source;
    lost.identity = exact::word{190'600U + projection.lost_count};
    lost.lineage += lost.identity.value();
    lost.retained = false;
  }
  bool scalar_seen[cm_degree_capacity + 1U]{};
  for (std::uint8_t vertex = 0; vertex < cm_point_capacity; ++vertex) {
    std::uint8_t sum = 0;
    for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
      sum = static_cast<std::uint8_t>(sum + projection.points[vertex].coefficients[slot]);
    }
    scalar_seen[sum] = true;
  }
  for (const auto seen : scalar_seen) {
    projection.distinct_scalar_sums = static_cast<std::uint8_t>(
        projection.distinct_scalar_sums + (seen ? 1U : 0U));
  }
  projection.exact = exact && projection.basis_injective &&
      projection.factor_expansion_agree && projection.projection_loss == 0;
}

HOLONICS_CALLABLE constexpr void form_scattering(cm_incidence_receipt& out) noexcept {
  auto& receipt = out.scattering;
  receipt.identity = exact::word{190'450};
  receipt.lineage = out.window.lineage + receipt.identity.value();
  for (std::uint8_t axis = 0; axis < cm_degree_capacity; ++axis) {
    for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
      for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
        std::int16_t first = 0;
        std::int16_t second = 0;
        for (std::uint8_t inner = 0; inner < cm_point_capacity; ++inner) {
          const auto axis_left = static_cast<std::uint8_t>(row ^ (1U << axis));
          const auto axis_right = static_cast<std::uint8_t>(inner ^ (1U << axis));
          first = static_cast<std::int16_t>(first +
              (inner == axis_left ? out.window.adjacency[inner][column] : 0));
          second = static_cast<std::int16_t>(second +
              (column == axis_right ? out.window.adjacency[row][inner] : 0));
        }
        const auto residual = static_cast<std::int16_t>(first - second);
        if (residual != 0) {
          ++receipt.commutator_nonzero[axis];
          receipt.commutator_square[axis] = static_cast<std::uint8_t>(
              receipt.commutator_square[axis] + residual * residual);
        }
      }
    }
  }
  receipt.interchange_broken = out.returned_translations == cm_translation_capacity;
  receipt.exact = true;
  for (std::uint8_t axis = 0; axis < cm_degree_capacity; ++axis) {
    receipt.exact = receipt.exact && (receipt.interchange_broken ?
        receipt.commutator_nonzero[axis] != 0 : receipt.commutator_nonzero[axis] == 0);
  }
}

}  // namespace holonics::organ::cm_window_detail
