#pragma once

#include <holonics/codec/rederivation_face.hpp>
#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::event::rederivation_surface_detail {

HOLONICS_CALLABLE inline void
form(const organ::rederivation_receipt &source,
     const organ::rederivation_workspace &workspace,
     codec::rederivation_surface &out) noexcept {
  out.passage = source.theory.passage;
  out.p_vandermonde = source.matching.p_vandermonde;
  out.q_vandermonde = source.matching.q_vandermonde;
  out.duplicate_q_vandermonde = source.matching.duplicate_q_vandermonde;
  out.coefficient_count = source.matching.coefficient_count;
  out.jacobian_count = source.matching.jacobian_entries;
  out.injection_count = static_cast<std::uint16_t>(
      source.matching.injection_count[0] + source.matching.injection_count[1]);
  for (std::size_t i = 0; i < organ::rederivation_jacobian_count; ++i) {
    const auto &entry = workspace.jacobian[i];
    out.jacobian[i] = {entry.value, entry.row_factor, entry.p_evaluation,
                       entry.q_evaluation};
  }
  for (std::size_t i = 0; i < organ::rederivation_coefficient_count; ++i) {
    const auto &factor = workspace.factors[i];
    out.factors[i] = {factor.p_leading, factor.q_leading, factor.row_factor};
  }
  for (std::size_t i = 0; i < organ::rederivation_polygon_count; ++i) {
    const auto &polygon = source.polygons[i];
    auto &returned = out.polygons[i];
    returned.area_twice = polygon.double_area;
    returned.boundary = polygon.boundary;
    returned.interior = polygon.interior;
    for (std::size_t n = 0; n < organ::rederivation_dilation_count; ++n) {
      returned.lattice_count[n] = polygon.lattice_count[n];
      returned.reciprocal_interior[n] = polygon.reciprocal_interior[n];
    }
  }
  for (std::size_t i = 0; i < 4; ++i)
    out.potential_matrix[i] = source.potential.matrix[i];
  for (std::size_t i = 0; i < 2; ++i) {
    out.potential_boundary[i] = source.potential.boundary[i];
    out.potential_solution[i] = source.potential.solution[i];
    out.potential_eigenvalues[i] = source.potential.eigenvalues[i];
  }
  for (std::size_t i = 0; i < 4; ++i)
    out.potential_eigenvectors[i] = source.potential.eigenvectors[i];
  for (std::size_t i = 0; i < 3; ++i) {
    out.potential_characteristic[i] = source.potential.characteristic[i];
    out.potential_energy[i] = source.potential.energy[i];
  }
  out.disconnected_determinant = source.potential.disconnected_determinant;
  for (std::size_t i = 0; i < organ::rederivation_pair_count; ++i) {
    const auto &pair = workspace.pairs[i];
    out.pairs[i] = {pair.x, pair.y, pair.witness, pair.left, pair.right};
  }
  for (std::size_t i = 0; i < 8; ++i) {
    out.cover_f[i] = source.cover.f[i];
    out.cover_g[i] = source.cover.g[i];
    out.cover_exceptional[i] = source.cover.exceptional[i];
  }
  out.cover_words = source.cover_card.words;
  out.cover_width = source.cover.width;
  out.subset_count = source.cover.subset_receipts;
  out.pair_count = source.cover.pair_receipts;
  out.width_one_collision[0] = source.cover.width_one_collision[0];
  out.width_one_collision[1] = source.cover.width_one_collision[1];
  out.width_two_collision[0] = source.cover.width_two_collision[0];
  out.width_two_collision[1] = source.cover.width_two_collision[1];
  out.self_crossing_obstructed = source.self_crossing_obstructed;
  out.all_exact = source.all_exact;
}

} // namespace holonics::event::rederivation_surface_detail
