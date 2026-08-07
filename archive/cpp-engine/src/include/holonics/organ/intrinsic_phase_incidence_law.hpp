#pragma once

#include <holonics/organ/intrinsic_hypergeometry_receipt.hpp>

namespace holonics::organ::intrinsic_hypergeometry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_card(
    const intrinsic_hypergeometry_card& card) noexcept {
  if (!card.parsed || card.schema.value() != 260'026 || card.occurrence.value() == 0 ||
      card.case_count != intrinsic_case_capacity || card.section_modulus != 65'521 ||
      card.receiver_first_weight != 3 || card.receiver_second_weight != 1 ||
      card.receiver_denominator != 3 || card.series_depth == 0 ||
      card.series_depth > intrinsic_series_capacity) { return false; }
  for (std::uint8_t slot = 0; slot < card.case_count; ++slot) {
    const auto& value = card.cases[slot];
    if (value.first < 2 || value.first > 19 || value.second < 2 || value.second > 19 ||
        value.rechart > 1 || value.first * value.second > intrinsic_vertex_capacity) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t vertex_index(
    std::uint16_t first, std::uint16_t second, std::uint16_t second_modulus) noexcept {
  return static_cast<std::uint16_t>(first * second_modulus + second);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_ratio(
    phase_ratio left, phase_ratio right) noexcept {
  return left.numerator == right.numerator && left.denominator == right.denominator;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool form_coordinates(
    const intrinsic_hypergeometry_card& card, intrinsic_phase_case_receipt& out) noexcept {
  const auto m = out.presentation.first; const auto n = out.presentation.second;
  for (std::uint16_t first = 0; first < m; ++first) {
    for (std::uint16_t second = 0; second < n; ++second) {
      auto& vertex = out.vertices[vertex_index(first, second, n)];
      if (!phase_crystal_detail::conic_phase(first, m,
              vertex.factor_coordinates[0], vertex.factor_coordinates[1]) ||
          !phase_crystal_detail::conic_phase(second, n,
              vertex.factor_coordinates[2], vertex.factor_coordinates[3])) { return false; }
      phase_ratio first_x{}; phase_ratio first_y{}; phase_ratio second_x{}; phase_ratio second_y{};
      if (!phase_crystal_detail::scale(vertex.factor_coordinates[0],
              card.receiver_first_weight, card.receiver_denominator, first_x) ||
          !phase_crystal_detail::scale(vertex.factor_coordinates[1],
              card.receiver_first_weight, card.receiver_denominator, first_y) ||
          !phase_crystal_detail::scale(vertex.factor_coordinates[2],
              card.receiver_second_weight, card.receiver_denominator, second_x) ||
          !phase_crystal_detail::scale(vertex.factor_coordinates[3],
              card.receiver_second_weight, card.receiver_denominator, second_y) ||
          !phase_crystal_detail::add(first_x, second_x, vertex.projected.x) ||
          !phase_crystal_detail::add(first_y, second_y, vertex.projected.y)) { return false; }
      vertex.projected.first = first; vertex.projected.second = second;
      vertex.lineage = out.lineage.value() + 1'000U + vertex_index(first, second, n);
    }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void form_edges_faces(intrinsic_phase_case_receipt& out) noexcept {
  const auto m = out.presentation.first; const auto n = out.presentation.second;
  const auto cells = out.vertex_count;
  for (std::uint16_t first = 0; first < m; ++first) {
    const auto next_first = static_cast<std::uint16_t>(first + 1U == m ? 0U : first + 1U);
    const auto prior_first = static_cast<std::uint16_t>(first == 0 ? m - 1U : first - 1U);
    for (std::uint16_t second = 0; second < n; ++second) {
      const auto next_second = static_cast<std::uint16_t>(second + 1U == n ? 0U : second + 1U);
      const auto prior_second = static_cast<std::uint16_t>(second == 0 ? n - 1U : second - 1U);
      const auto source = vertex_index(first, second, n);
      auto& horizontal = out.edges[source]; auto& vertical = out.edges[cells + source];
      horizontal = {out.lineage.value() + 2'000U + source, source,
          vertex_index(next_first, second, n),
          {source, vertex_index(first, prior_second, n)}, {1, -1}, 0,
          next_first == 0};
      vertical = {out.lineage.value() + 3'000U + source, source,
          vertex_index(first, next_second, n),
          {vertex_index(prior_first, second, n), source}, {1, -1}, 1,
          next_second == 0};
      auto& face = out.faces[source];
      face.lineage = out.lineage.value() + 4'000U + source;
      face.vertices[0] = source; face.vertices[1] = vertex_index(next_first, second, n);
      face.vertices[2] = vertex_index(next_first, next_second, n);
      face.vertices[3] = vertex_index(first, next_second, n);
      face.edges[0] = source;
      face.edges[1] = static_cast<std::uint16_t>(cells + face.vertices[1]);
      face.edges[2] = vertex_index(first, next_second, n);
      face.edges[3] = static_cast<std::uint16_t>(cells + source);
      face.orientations[0] = 1; face.orientations[1] = 1;
      face.orientations[2] = -1; face.orientations[3] = -1; face.filled = true;
    }
  }
}

HOLONICS_CALLABLE constexpr void form_stars_flags(intrinsic_phase_case_receipt& out) noexcept {
  const auto m = out.presentation.first; const auto n = out.presentation.second;
  const auto cells = out.vertex_count;
  for (std::uint16_t first = 0; first < m; ++first) {
    const auto next_first = static_cast<std::uint16_t>(first + 1U == m ? 0U : first + 1U);
    const auto prior_first = static_cast<std::uint16_t>(first == 0 ? m - 1U : first - 1U);
    for (std::uint16_t second = 0; second < n; ++second) {
      const auto next_second = static_cast<std::uint16_t>(second + 1U == n ? 0U : second + 1U);
      const auto prior_second = static_cast<std::uint16_t>(second == 0 ? n - 1U : second - 1U);
      const auto index = vertex_index(first, second, n); auto& vertex = out.vertices[index];
      vertex.star_edges[0] = index; vertex.star_edges[1] = vertex_index(prior_first, second, n);
      vertex.star_edges[2] = static_cast<std::uint16_t>(cells + index);
      vertex.star_edges[3] = static_cast<std::uint16_t>(cells + vertex_index(first, prior_second, n));
      vertex.star_faces[0] = index; vertex.star_faces[1] = vertex_index(prior_first, second, n);
      vertex.star_faces[2] = vertex_index(first, prior_second, n);
      vertex.star_faces[3] = vertex_index(prior_first, prior_second, n);
      vertex.link_vertices[0] = vertex_index(next_first, second, n);
      vertex.link_vertices[1] = vertex_index(first, next_second, n);
      vertex.link_vertices[2] = vertex_index(prior_first, second, n);
      vertex.link_vertices[3] = vertex_index(first, prior_second, n);
    }
  }
  constexpr std::uint8_t flag_vertices[8]{0,1,1,2,2,3,3,0};
  constexpr std::uint8_t flag_edges[8]{0,0,1,1,2,2,3,3};
  for (std::uint16_t face = 0; face < out.face_count; ++face) {
    for (std::uint8_t local = 0; local < 8; ++local) {
      auto& flag = out.flags[8U * face + local];
      flag.lineage = out.faces[face].lineage + 100U + local;
      flag.vertex = out.faces[face].vertices[flag_vertices[local]];
      flag.edge = out.faces[face].edges[flag_edges[local]]; flag.face = face;
      flag.orientation = out.faces[face].orientations[flag_edges[local]];
    }
  }
}

}  // namespace holonics::organ::intrinsic_hypergeometry_detail
