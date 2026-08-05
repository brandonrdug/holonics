#pragma once

#include <holonics/codec/causal_linear_face.hpp>
#include <holonics/organ/causal_linear_receipt.hpp>

namespace holonics::event {

[[nodiscard]] HOLONICS_CALLABLE constexpr codec::causal_linear_surface causal_linear_surface(
    const organ::causal_linear_receipt& inquiry) noexcept {
  codec::causal_linear_surface surface{}; surface.passage = inquiry.theory.passage;
  surface.phase_counts[0] = inquiry.phase.vertices;
  surface.phase_counts[1] = inquiry.phase.edges;
  surface.phase_counts[2] = inquiry.phase.faces;
  surface.phase_ranks[0] = inquiry.phase.boundary_one_analysis.rank;
  surface.phase_ranks[1] = inquiry.phase.boundary_two_analysis.rank;
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    surface.phase_betti[slot] = inquiry.phase.betti[slot];
  }
  surface.phase_tours = inquiry.phase.tours;
  surface.phase_tour_length = inquiry.phase.tour_length;
  surface.cm_rank = inquiry.cm.incidence_analysis.rank;
  surface.cm_homology[0] = inquiry.cm.homology_zero;
  surface.cm_homology[1] = inquiry.cm.homology_one;
  surface.factor_count = inquiry.cm.factor_count;
  for (std::uint8_t slot = 0; slot < 17; ++slot) {
    surface.cm_characteristic[slot] = inquiry.cm.adjacency_characteristic.coefficients[slot];
  }
  for (std::uint8_t slot = 0; slot < inquiry.cm.factor_count; ++slot) {
    surface.cm_factor_roots[slot] = inquiry.cm.factor_roots[slot];
    surface.cm_factor_multiplicities[slot] = inquiry.cm.factor_multiplicities[slot];
  }
  for (std::uint8_t fan = 0; fan < 2; ++fan) {
    surface.toric_cokernel[fan] = inquiry.toric.source[fan].free_cokernel_rank;
    surface.toric_smith[fan][0] = inquiry.toric.source[fan].smith[0];
    surface.toric_smith[fan][1] = inquiry.toric.source[fan].smith[1];
  }
  surface.toric_cokernel[2] = inquiry.toric.blowup.free_cokernel_rank;
  surface.toric_smith[2][0] = inquiry.toric.blowup.smith[0];
  surface.toric_smith[2][1] = inquiry.toric.blowup.smith[1];
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      surface.form[row][column] = inquiry.variation.form[row][column];
      for (std::uint8_t coefficient = 0; coefficient < 2; ++coefficient) {
        surface.pencil[row][column][coefficient] =
            inquiry.variation.pencil[row][column][coefficient];
      }
      for (std::uint8_t loop = 0; loop < 3; ++loop) {
        surface.loops[loop][row][column] = inquiry.variation.loops[loop][row][column];
      }
    }
  }
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    surface.determinant[slot] = inquiry.variation.determinant[slot];
    surface.identity_characteristic[slot] =
        inquiry.controls.identity_characteristic.coefficients[slot];
    surface.jordan_characteristic[slot] =
        inquiry.controls.jordan_characteristic.coefficients[slot];
  }
  surface.identity_fixed = inquiry.controls.identity_fixed;
  surface.jordan_fixed = inquiry.controls.jordan_fixed;
  surface.chain_exact = inquiry.phase.boundary_composite_zero && inquiry.cm.exact;
  surface.characteristics_exact = inquiry.phase.diagonal_characteristic.exact &&
      inquiry.cm.adjacency_characteristic.exact && inquiry.variation.tensor_characteristic.exact;
  surface.multilinear_exact = inquiry.variation.adjoints_exact &&
      inquiry.variation.exterior_exact && inquiry.variation.tensor.exact;
  surface.controls_exact = inquiry.controls.exact;
  surface.alternatives_retained = inquiry.alternatives_retained;
  return surface;
}

}  // namespace holonics::event
