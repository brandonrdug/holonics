#pragma once

#include <holonics/organ/elementary_calculus_receipt.hpp>

namespace holonics::organ::occurrence_incidence_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::uint8_t population(std::uint8_t mask) noexcept {
  std::uint8_t count = 0;
  for (; mask != 0; mask >>= 1U) count += static_cast<std::uint8_t>(mask & 1U);
  return count;
}

HOLONICS_CALLABLE inline void derive_identity(const occurrence_incidence_card &card,
    occurrence_incidence_receipt &out) noexcept {
  std::uint8_t best = elementary_coordinate_count + 1U;
  for (std::uint8_t mask = 1; mask < 32; ++mask) {
    auto &candidate = out.masks[mask - 1U]; candidate.mask = mask;
    candidate.fields = population(mask);
    for (std::uint8_t left = 0; left < card.occurrence_count; ++left)
      for (std::uint8_t right = left + 1U; right < card.occurrence_count; ++right) {
        bool equal = true;
        for (std::uint8_t field = 0; field < elementary_coordinate_count; ++field)
          if ((mask & (1U << field)) != 0)
            equal = equal && card.coordinates[left][field] == card.coordinates[right][field];
        if (equal) ++candidate.collisions;
      }
    candidate.obstruction = candidate.collisions == 0 ? elementary_obstruction::none :
        elementary_obstruction::collision;
    if (candidate.collisions == 0 && candidate.fields < best) {
      best = candidate.fields; out.selected_mask = mask;
    }
  }
  for (auto &candidate : out.masks)
    candidate.selected = candidate.mask == out.selected_mask;
  out.payload_collapse_refuted = true;
  for (std::uint8_t i = 1; i < card.occurrence_count; ++i)
    out.payload_collapse_refuted = out.payload_collapse_refuted &&
        card.payload[i] == card.payload[0];
}

HOLONICS_CALLABLE inline void boundary_product(const occurrence_incidence_card &card,
    std::uint8_t candidate, boundary_candidate_receipt &out) noexcept {
  out.candidate = candidate;
  for (std::uint8_t vertex = 0; vertex < 4; ++vertex)
    for (std::uint8_t face = 0; face < elementary_face_count; ++face)
      for (std::uint8_t edge = 0; edge < elementary_edge_count; ++edge) {
        std::int64_t one = card.boundary_one[vertex][edge];
        std::int64_t two = card.boundary_two[edge][face];
        if (candidate == 1) { if (one < 0) one = -one; if (two < 0) two = -two; }
        if (candidate == 2 && edge == 2) { one = -one; two = -two; }
        if (candidate == 3 && edge == 2) one = -one;
        out.residual[vertex][face] += one * two;
      }
  bool zero = true;
  for (const auto &row : out.residual) for (const auto value : row) zero = zero && value == 0;
  out.diagonal_cancelled = candidate != 1 &&
      (candidate == 2 ? -card.boundary_two[2][0] - card.boundary_two[2][1] :
                        card.boundary_two[2][0] + card.boundary_two[2][1]) == 0;
  out.obstruction = zero ? elementary_obstruction::none : elementary_obstruction::nonzero_boundary;
  out.selected = candidate == 0 && zero;
}

HOLONICS_CALLABLE inline void derive(const occurrence_incidence_card &card,
    occurrence_incidence_receipt &out) noexcept {
  derive_identity(card, out);
  for (std::uint8_t candidate = 0; candidate < 4; ++candidate)
    boundary_product(card, candidate, out.boundaries[candidate]);
  out.boundary_squared_zero = out.boundaries[0].obstruction == elementary_obstruction::none;
  out.coherent_reorientation_exact =
      out.boundaries[2].obstruction == elementary_obstruction::none;
  out.theory_formed = out.selected_mask == 31 && out.payload_collapse_refuted &&
      out.boundary_squared_zero && out.coherent_reorientation_exact &&
      out.boundaries[1].obstruction == elementary_obstruction::nonzero_boundary &&
      out.boundaries[3].obstruction == elementary_obstruction::nonzero_boundary;
}

}  // namespace holonics::organ::occurrence_incidence_detail
