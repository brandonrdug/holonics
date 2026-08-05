#pragma once

#include <holonics/organ/causal_linear_characteristic.hpp>

namespace holonics::organ::causal_linear_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t phase_vertex(
    std::uint8_t first, std::uint8_t second, std::uint8_t second_modulus) noexcept {
  return static_cast<std::uint8_t>(first * second_modulus + second);
}

HOLONICS_CALLABLE constexpr void derive_phase(const causal_linear_card& card,
    causal_phase_section& out) noexcept {
  out.identity = exact::word{192'410};
  out.lineage = exact::word{card.lineage.value() + 10U};
  const auto first = card.phase_first; const auto second = card.phase_second;
  const auto vertices = static_cast<std::uint8_t>(first * second);
  const auto edges = static_cast<std::uint8_t>(2U * vertices);
  if (!card.parsed || first < 2 || second < 2 || vertices > causal_matrix_rows ||
      edges > causal_matrix_columns) { return; }
  out.vertices = vertices; out.edges = edges; out.faces = vertices;
  set_matrix(out.boundary_one, vertices, edges, 192'411, out.lineage.value() + 1U);
  set_matrix(out.boundary_two, edges, vertices, 192'412, out.lineage.value() + 2U);
  set_matrix(out.diagonal, vertices, vertices, 192'413, out.lineage.value() + 3U);
  for (std::uint8_t i = 0; i < first; ++i) {
    for (std::uint8_t j = 0; j < second; ++j) {
      const auto source = phase_vertex(i, j, second);
      const auto next_i = static_cast<std::uint8_t>(
          i + 1U < first ? i + 1U : 0U);
      const auto next_j = static_cast<std::uint8_t>(
          j + 1U < second ? j + 1U : 0U);
      const auto horizontal = source;
      const auto vertical = static_cast<std::uint8_t>(vertices + source);
      const auto horizontal_target = phase_vertex(next_i, j, second);
      const auto vertical_target = phase_vertex(i, next_j, second);
      out.boundary_one.values[source][horizontal] = -1;
      out.boundary_one.values[horizontal_target][horizontal] = 1;
      out.boundary_one.values[source][vertical] = -1;
      out.boundary_one.values[vertical_target][vertical] = 1;
      const auto top = phase_vertex(i, next_j, second);
      const auto right = phase_vertex(next_i, j, second);
      out.boundary_two.values[horizontal][source] = 1;
      out.boundary_two.values[static_cast<std::uint8_t>(vertices + right)][source] = 1;
      out.boundary_two.values[top][source] = -1;
      out.boundary_two.values[vertical][source] = -1;
      const auto diagonal_target = phase_vertex(next_i, next_j, second);
      out.diagonal.values[diagonal_target][source] = 1;
      out.vertex_lineage[source] = card.lineage.value() + 100U + source;
      out.edge_lineage[horizontal] = card.lineage.value() + 200U + horizontal;
      out.edge_lineage[vertical] = card.lineage.value() + 200U + vertical;
      out.face_lineage[source] = card.lineage.value() + 300U + source;
    }
  }
  analyze(out.boundary_one, out.boundary_one_analysis, 192'414);
  analyze(out.boundary_two, out.boundary_two_analysis, 192'415);
  causal_integer_matrix composite{};
  out.boundary_composite_zero = multiply(
      out.boundary_one, out.boundary_two, composite, 192'416) && zero(composite);
  characteristic(out.diagonal, out.diagonal_characteristic, 192'417);
  const auto divisor = static_cast<std::uint8_t>(exact::small_rational_law::gcd(first, second));
  out.tours = divisor;
  out.tour_length = static_cast<std::uint8_t>(exact::small_rational_law::quotient(
      static_cast<std::int64_t>(first), static_cast<std::int64_t>(divisor)) * second);
  out.betti[0] = static_cast<std::uint8_t>(vertices - out.boundary_one_analysis.rank);
  out.betti[1] = static_cast<std::uint8_t>(edges - out.boundary_one_analysis.rank -
      out.boundary_two_analysis.rank);
  out.betti[2] = static_cast<std::uint8_t>(vertices - out.boundary_two_analysis.rank);
  out.exact = out.boundary_one_analysis.exact && out.boundary_two_analysis.exact &&
      out.boundary_composite_zero && out.diagonal_characteristic.exact &&
      out.betti[0] == 1 && out.betti[1] == 2 && out.betti[2] == 1 &&
      static_cast<std::uint8_t>(out.tours * out.tour_length) == vertices;
}

}  // namespace holonics::organ::causal_linear_detail
