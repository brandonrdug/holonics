#pragma once

#include <holonics/organ/intrinsic_phase_incidence_law.hpp>

namespace holonics::organ::intrinsic_hypergeometry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t common_vertices(
    const intrinsic_face_receipt& left, const intrinsic_face_receipt& right) noexcept {
  std::uint8_t count = 0;
  for (const auto first : left.vertices) {
    bool found = false;
    for (const auto second : right.vertices) { found = found || first == second; }
    count = static_cast<std::uint8_t>(count + (found ? 1U : 0U));
  }
  return count;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t common_edges(
    const intrinsic_face_receipt& left, const intrinsic_face_receipt& right) noexcept {
  std::uint8_t count = 0;
  for (const auto first : left.edges) {
    bool found = false;
    for (const auto second : right.edges) { found = found || first == second; }
    count = static_cast<std::uint8_t>(count + (found ? 1U : 0U));
  }
  return count;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool close_boundaries(
    intrinsic_phase_case_receipt& out) noexcept {
  bool exact = true;
  for (std::uint16_t face_index = 0; face_index < out.face_count; ++face_index) {
    std::int8_t balance[intrinsic_vertex_capacity]{}; const auto& face = out.faces[face_index];
    for (std::uint8_t local = 0; local < 4; ++local) {
      const auto& edge = out.edges[face.edges[local]]; const auto sign = face.orientations[local];
      balance[edge.source] = static_cast<std::int8_t>(balance[edge.source] - sign);
      balance[edge.target] = static_cast<std::int8_t>(balance[edge.target] + sign);
    }
    bool closes = true;
    for (std::uint16_t vertex = 0; vertex < out.vertex_count; ++vertex) {
      closes = closes && balance[vertex] == 0;
    }
    out.faces[face_index].boundary_closes = closes; exact = exact && closes;
  }
  out.boundaries_exact = exact; return exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool close_shared_seams(
    intrinsic_phase_case_receipt& out) noexcept {
  bool exact = true;
  for (std::uint16_t edge = 0; edge < out.edge_count; ++edge) {
    const auto& value = out.edges[edge];
    exact = exact && value.incident_faces[0] < out.face_count &&
        value.incident_faces[1] < out.face_count &&
        value.incident_faces[0] != value.incident_faces[1] &&
        value.incident_orientation[0] + value.incident_orientation[1] == 0;
  }
  out.seams_shared_exact = exact; return exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool form_projection_fibers(
    intrinsic_phase_case_receipt& out) noexcept {
  out.projection_fiber_count = 0;
  for (std::uint16_t vertex = 0; vertex < out.vertex_count; ++vertex) {
    std::uint16_t found = out.projection_fiber_count;
    for (std::uint16_t prior = 0; prior < vertex; ++prior) {
      if (same_ratio(out.vertices[vertex].projected.x, out.vertices[prior].projected.x) &&
          same_ratio(out.vertices[vertex].projected.y, out.vertices[prior].projected.y)) {
        found = out.vertices[prior].projection_fiber; break;
      }
    }
    if (found == out.projection_fiber_count) { ++out.projection_fiber_count; }
    out.vertices[vertex].projection_fiber = found; ++out.projection_fiber_sizes[found];
  }
  std::uint16_t returned = 0;
  for (std::uint16_t fiber = 0; fiber < out.projection_fiber_count; ++fiber) {
    returned = static_cast<std::uint16_t>(returned + out.projection_fiber_sizes[fiber]);
  }
  out.projection_fibers_complete = returned == out.vertex_count;
  return out.projection_fibers_complete;
}

HOLONICS_CALLABLE constexpr void form_face_intersections(
    intrinsic_phase_case_receipt& out) noexcept {
  for (std::uint16_t left = 0; left < out.face_count; ++left) {
    for (std::uint16_t right = static_cast<std::uint16_t>(left + 1U);
        right < out.face_count; ++right) {
      const auto vertices = common_vertices(out.faces[left], out.faces[right]);
      const auto edges = common_edges(out.faces[left], out.faces[right]);
      if (vertices <= 4 && edges <= 4) { ++out.face_intersections[vertices][edges]; }
    }
  }
}

HOLONICS_CALLABLE constexpr void derive_phase_incidence(
    const intrinsic_hypergeometry_foundation& foundation, std::uint8_t slot,
    intrinsic_phase_case_receipt& out) noexcept {
  constexpr std::uint64_t identities[intrinsic_case_capacity]{193'410,193'411,193'412,
      193'413,193'414,193'415,193'416,193'417,193'418,193'419};
  if (!valid_card(foundation.card) || slot >= foundation.card.case_count) { return; }
  out.identity = exact::word{identities[slot]};
  out.lineage = exact::word{foundation.card.lineage.value() + identities[slot]};
  out.presentation = foundation.card.cases[slot];
  const auto divisor = phase_crystal_detail::gcd(
      out.presentation.first, out.presentation.second);
  std::uint64_t quotient = 0; std::uint64_t remainder = 0;
  if (divisor == 0 || !phase_crystal_detail::divide_unsigned(
          out.presentation.first, divisor, quotient, remainder) || remainder != 0) { return; }
  out.gcd = static_cast<std::uint16_t>(divisor);
  out.lcm = static_cast<std::uint16_t>(quotient * out.presentation.second);
  out.vertex_count = static_cast<std::uint16_t>(
      out.presentation.first * out.presentation.second);
  out.edge_count = static_cast<std::uint16_t>(2U * out.vertex_count);
  out.face_count = out.vertex_count;
  out.flag_count = static_cast<std::uint16_t>(8U * out.face_count);
  out.tour_count = static_cast<std::uint8_t>(out.gcd);
  out.recurrence_depth = static_cast<std::uint16_t>(
      (out.presentation.first > out.presentation.second ? out.presentation.first :
       out.presentation.second) + 1U);
  out.coordinates_exact = form_coordinates(foundation.card, out);
  form_edges_faces(out); form_stars_flags(out);
  out.boundaries_exact = close_boundaries(out);
  out.seams_shared_exact = close_shared_seams(out);
  out.stars_links_exact = out.flag_count == 8U * out.face_count;
  out.projection_fibers_complete = form_projection_fibers(out);
  form_face_intersections(out);
  out.incidence_exact = out.coordinates_exact && out.boundaries_exact &&
      out.seams_shared_exact && out.stars_links_exact && out.projection_fibers_complete;
}

}  // namespace holonics::organ::intrinsic_hypergeometry_detail
