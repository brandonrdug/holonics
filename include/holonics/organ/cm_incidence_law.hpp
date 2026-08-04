#pragma once

#include <holonics/organ/cm_characteristic_law.hpp>

namespace holonics::organ::cm_incidence_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t popcount(
    std::uint8_t value) noexcept {
  std::uint8_t count = 0;
  while (value != 0) {
    count = static_cast<std::uint8_t>(count + (value & 1U));
    value = static_cast<std::uint8_t>(value >> 1U);
  }
  return count;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_card(
    const cm_problem_card& card) noexcept {
  return card.parsed && card.schema.value() == 210'023 && card.occurrence.value() != 0 &&
      card.cyclotomic_order == 5 && card.degree == cm_degree_capacity &&
      card.periodic_modulus == 2 && card.window_min == 0 && card.window_max == 1 &&
      card.translation_count >= 4 && card.translation_count <= cm_translation_capacity &&
      card.factor_min <= -5 && card.factor_max >= 5;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const cm_incidence_foundation& value) noexcept {
  return value.ecology.value() != 0 && value.arithmetic.value() != 0 &&
      value.translation.value() != 0 && value.incidence.value() != 0 &&
      value.characteristic.value() != 0 && value.projection.value() != 0 &&
      value.provenance.value() != 0 && valid_card(value.card);
}

HOLONICS_CALLABLE constexpr void form_translations(
    const cm_problem_card& card, cm_incidence_receipt& out) noexcept {
  if (!valid_card(card)) { out.obstruction = cm_obstruction::arithmetic_refused; return; }
  cm_element value = cm_arithmetic_detail::one();
  const auto z = cm_arithmetic_detail::generator();
  bool all_exact = true;
  for (std::uint8_t slot = 0; slot < card.translation_count; ++slot) {
    auto& receipt = out.translations[slot];
    bool exact = true;
    receipt.identity = exact::word{190'410U + slot};
    receipt.value = value;
    receipt.conjugate = cm_arithmetic_detail::conjugate(value, exact);
    receipt.norm = cm_arithmetic_detail::multiply(value, receipt.conjugate, exact);
    receipt.residue_mask = cm_arithmetic_detail::residue_mask(value);
    receipt.lineage = card.lineage.value() + receipt.identity.value();
    receipt.norm_one = cm_arithmetic_detail::equal(
        receipt.norm, cm_arithmetic_detail::one());
    receipt.exact = exact && receipt.norm_one && receipt.residue_mask != 0;
    all_exact = all_exact && receipt.exact;
    value = cm_arithmetic_detail::multiply(value, z, all_exact);
    ++out.returned_translations;
  }
  out.mounted = card;
  out.no_expected_incidence = true;
  out.no_expected_spectrum = true;
  if (!all_exact) { out.obstruction = cm_obstruction::arithmetic_refused; }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t direction_of(
    const cm_element& difference, const cm_incidence_receipt& receipt) noexcept {
  for (std::uint8_t slot = 0; slot < receipt.returned_translations; ++slot) {
    if (cm_arithmetic_detail::equal(difference, receipt.translations[slot].value) ||
        cm_arithmetic_detail::equal(difference,
            cm_arithmetic_detail::negate(receipt.translations[slot].value))) { return slot; }
  }
  return cm_translation_capacity;
}

HOLONICS_CALLABLE constexpr void append_edge(cm_graph_receipt& graph,
    std::uint8_t source, std::uint8_t target, std::uint8_t direction,
    std::uint64_t lineage) noexcept {
  if (graph.edge_count >= cm_edge_capacity) { return; }
  auto& edge = graph.edges[graph.edge_count];
  edge.identity = exact::word{190'500U + graph.edge_count};
  edge.source = source;
  edge.target = target;
  edge.direction = direction;
  edge.lineage = lineage + edge.identity.value() + direction;
  edge.retained = true;
  ++graph.edge_count;
}

HOLONICS_CALLABLE constexpr void form_periodic(cm_incidence_receipt& out) noexcept {
  auto& graph = out.periodic;
  graph.identity = exact::word{190'420};
  graph.lineage = out.mounted.lineage.value() + graph.identity.value();
  bool commuting = true;
  for (std::uint8_t source = 0; source < cm_point_capacity; ++source) {
    for (std::uint8_t direction = 0; direction < out.returned_translations; ++direction) {
      const auto target = static_cast<std::uint8_t>(
          source ^ out.translations[direction].residue_mask);
      graph.adjacency[source][target] = 1;
      if (source < target) {
        append_edge(graph, source, target, direction,
            out.translations[direction].lineage);
      }
    }
    for (std::uint8_t left = 0; left < out.returned_translations; ++left) {
      for (std::uint8_t right = 0; right < out.returned_translations; ++right) {
        const auto first = static_cast<std::uint8_t>(source ^
            out.translations[left].residue_mask ^ out.translations[right].residue_mask);
        const auto second = static_cast<std::uint8_t>(source ^
            out.translations[right].residue_mask ^ out.translations[left].residue_mask);
        commuting = commuting && first == second;
      }
    }
  }
  graph.symmetric = true;
  bool eigen_exact = true;
  for (std::uint8_t frequency = 0; frequency < cm_point_capacity; ++frequency) {
    std::int16_t eigenvalue = 0;
    for (std::uint8_t direction = 0; direction < out.returned_translations; ++direction) {
      const auto overlap = popcount(static_cast<std::uint8_t>(
          frequency & out.translations[direction].residue_mask));
      eigenvalue = static_cast<std::int16_t>(
          eigenvalue + ((overlap & 1U) == 0 ? 1 : -1));
    }
    graph.character_eigenvalue[frequency] = eigenvalue;
    for (std::uint8_t vertex = 0; vertex < cm_point_capacity; ++vertex) {
      std::int16_t image = 0;
      for (std::uint8_t target = 0; target < cm_point_capacity; ++target) {
        const auto overlap = popcount(
            static_cast<std::uint8_t>(frequency & target));
        const auto character = static_cast<std::int16_t>((overlap & 1U) == 0 ? 1 : -1);
        image = static_cast<std::int16_t>(image + graph.adjacency[vertex][target] * character);
      }
      const auto overlap = popcount(
          static_cast<std::uint8_t>(frequency & vertex));
      const auto source_character = static_cast<std::int16_t>((overlap & 1U) == 0 ? 1 : -1);
      eigen_exact = eigen_exact && image == eigenvalue * source_character;
    }
  }
  for (std::uint8_t row = 0; row < cm_point_capacity; ++row) {
    for (std::uint8_t column = 0; column < cm_point_capacity; ++column) {
      graph.degree[row] = static_cast<std::uint8_t>(
          graph.degree[row] + graph.adjacency[row][column]);
      graph.symmetric = graph.symmetric &&
          graph.adjacency[row][column] == graph.adjacency[column][row];
    }
  }
  graph.exact = commuting && eigen_exact && graph.symmetric;
}

}  // namespace holonics::organ::cm_incidence_detail
