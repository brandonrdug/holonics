#pragma once

#include <holonics/organ/intrinsic_section_law.hpp>

namespace holonics::organ::intrinsic_hypergeometry_detail {

HOLONICS_CALLABLE constexpr void modular_action(const intrinsic_local_system_receipt& local,
    intrinsic_seam seam, std::uint8_t rechart, std::uint32_t modulus,
    std::uint32_t out[4]) noexcept {
  const std::int64_t identity[2][2]{{1,0},{0,1}};
  const std::int64_t (*source)[2] = identity;
  if (seam == intrinsic_seam::first) { source = local.positive[0]; }
  else if (seam == intrinsic_seam::second) { source = local.positive[1]; }
  else if (seam == intrinsic_seam::simultaneous) {
    source = rechart == 0 ? local.ordered_first : local.ordered_second;
  }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      out[2U * row + column] = reduce_mod(source[row][column], modulus);
    }
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr intrinsic_seam seam_at(
    std::uint16_t first, std::uint16_t second,
    const intrinsic_presentation& presentation) noexcept {
  const bool first_wrap = first + 1U == presentation.first;
  const bool second_wrap = second + 1U == presentation.second;
  if (first_wrap && second_wrap) { return intrinsic_seam::simultaneous; }
  if (first_wrap) { return intrinsic_seam::first; }
  if (second_wrap) { return intrinsic_seam::second; }
  return intrinsic_seam::interior;
}

HOLONICS_CALLABLE constexpr void form_chronology(
    const intrinsic_hypergeometry_foundation& foundation,
    const intrinsic_local_system_receipt& local, intrinsic_phase_case_receipt& out) noexcept {
  if (!out.incidence_exact || !local.exact ||
      out.recurrence_depth > foundation.card.series_depth) { return; }
  const auto m = out.presentation.first; const auto n = out.presentation.second;
  for (std::uint16_t first = 0; first < m; ++first) {
    for (std::uint16_t second = 0; second < n; ++second) {
      const auto index = vertex_index(first, second, n);
      const auto next_first = static_cast<std::uint16_t>(first + 1U == m ? 0U : first + 1U);
      const auto next_second = static_cast<std::uint16_t>(second + 1U == n ? 0U : second + 1U);
      auto& vertex = out.vertices[index]; vertex.successor = vertex_index(next_first, next_second, n);
      vertex.seam = seam_at(first, second, out.presentation);
      ++out.seam_receiver_fibers[static_cast<std::uint8_t>(vertex.seam)];
    }
  }
  for (std::uint16_t vertex = 0; vertex < out.vertex_count; ++vertex) {
    const auto next = out.vertices[vertex].successor;
    ++out.transition_population[static_cast<std::uint8_t>(out.vertices[vertex].seam)]
        [static_cast<std::uint8_t>(out.vertices[next].seam)];
  }
  bool visited[intrinsic_vertex_capacity]{}; std::uint8_t returned_tours = 0;
  for (std::uint16_t seed = 0; seed < out.vertex_count; ++seed) {
    if (visited[seed]) { continue; }
    auto& tour = out.tours[returned_tours]; tour.first_vertex = seed;
    std::uint32_t state[4]{1,0,0,1}; std::uint16_t current = seed;
    do {
      visited[current] = true; auto& vertex = out.vertices[current];
      vertex.tour = returned_tours; vertex.tour_position = tour.length;
      std::uint32_t action[4]{}; std::uint32_t next_state[4]{};
      modular_action(local, vertex.seam, out.presentation.rechart,
          foundation.card.section_modulus, action);
      modular_multiply(action, state, foundation.card.section_modulus, next_state);
      for (std::uint8_t slot = 0; slot < 4; ++slot) {
        state[slot] = next_state[slot]; vertex.section_after[slot] = state[slot];
      }
      tour.word_fold ^= static_cast<std::uint8_t>(vertex.seam) + 0x9e37'79b9U +
          (tour.word_fold << 6U) + (tour.word_fold >> 2U);
      ++tour.length; current = vertex.successor;
    } while (current != seed && tour.length <= out.lcm);
    for (std::uint8_t slot = 0; slot < 4; ++slot) { tour.return_matrix[slot] = state[slot]; }
    std::uint64_t quotient = 0; std::uint64_t cross_residue = 0;
    const bool cross_divided = phase_crystal_detail::divide_unsigned(
        static_cast<std::uint64_t>(state[1]) * state[2],
        foundation.card.section_modulus, quotient, cross_residue);
    const std::uint64_t determinant = static_cast<std::uint64_t>(state[0]) * state[3] +
        foundation.card.section_modulus - cross_residue;
    std::uint64_t determinant_residue = 0;
    const bool determinant_divided = phase_crystal_detail::divide_unsigned(
        determinant, foundation.card.section_modulus, quotient, determinant_residue);
    tour.determinant_one = cross_divided && determinant_divided &&
        determinant_residue == 1 && tour.length == out.lcm;
    ++returned_tours;
  }
  out.tour_count = returned_tours; out.seam_receiver_hull_corners = 4;
  std::uint32_t row_sum = 0;
  for (std::uint8_t row = 0; row < 4; ++row) {
    std::uint32_t local_sum = 0;
    for (std::uint8_t column = 0; column < 4; ++column) {
      local_sum += out.transition_population[row][column];
    }
    row_sum += local_sum;
    out.distributions_exact = out.distributions_exact || row == 0;
    out.distributions_exact = out.distributions_exact &&
        local_sum == out.seam_receiver_fibers[row];
  }
  out.chronology_exact = returned_tours == out.gcd;
  out.sections_exact = out.chronology_exact && row_sum == out.vertex_count;
  for (std::uint8_t tour = 0; tour < returned_tours; ++tour) {
    out.sections_exact = out.sections_exact && out.tours[tour].determinant_one;
  }
  out.exact = out.incidence_exact && out.distributions_exact && out.sections_exact;
}

}  // namespace holonics::organ::intrinsic_hypergeometry_detail
