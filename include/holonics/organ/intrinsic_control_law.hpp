#pragma once

#include <holonics/organ/intrinsic_supported_cycle_law.hpp>

namespace holonics::organ::intrinsic_hypergeometry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool unequal_return(
    const intrinsic_phase_case_receipt& left,
    const intrinsic_phase_case_receipt& right) noexcept {
  if (left.tour_count == 0 || right.tour_count == 0) { return false; }
  if (left.tours[0].word_fold != right.tours[0].word_fold) { return true; }
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    if (left.tours[0].return_matrix[slot] != right.tours[0].return_matrix[slot]) { return true; }
  }
  return false;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool unequal_transitions(
    const intrinsic_phase_case_receipt& left,
    const intrinsic_phase_case_receipt& right) noexcept {
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      if (left.transition_population[row][column] !=
          right.transition_population[row][column]) { return true; }
    }
  }
  return false;
}

HOLONICS_CALLABLE constexpr void form_rebase_control(
    const intrinsic_hypergeometry_foundation& foundation,
    const intrinsic_phase_case_receipt& left,
    const intrinsic_phase_case_receipt& right,
    intrinsic_control_receipt& out) noexcept {
  if (left.tour_count != 1 || right.tour_count != 1) { return; }
  const auto modulus = foundation.card.section_modulus;
  const std::uint32_t j[4]{0,1,modulus - 1U,0};
  const std::uint32_t inverse[4]{0,modulus - 1U,1,0};
  std::uint32_t front[4]{};
  modular_multiply(j, left.tours[0].return_matrix, modulus, front);
  modular_multiply(front, inverse, modulus, out.rebase_left);
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    out.rebase_right[slot] = right.tours[0].return_matrix[slot];
  }
  out.conjugate_rechart = true;
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    out.conjugate_rechart = out.conjugate_rechart &&
        out.rebase_left[slot] == out.rebase_right[slot];
  }
}

HOLONICS_CALLABLE constexpr void derive_controls(
    const intrinsic_hypergeometry_foundation& foundation,
    intrinsic_hypergeometry_receipt& out) noexcept {
  auto& controls = out.controls;
  const auto& first = out.cases[2]; const auto& larger = out.cases[3];
  const auto& rechart = out.cases[9];
  controls.equal_hull_unequal_transport = first.seam_receiver_hull_corners == 4 &&
      larger.seam_receiver_hull_corners == 4 && unequal_return(first, larger);
  controls.equal_local_population_unequal_order = first.stars_links_exact &&
      larger.stars_links_exact && unequal_transitions(first, larger);
  controls.equal_spectrum_unequal_support = out.supported.common_cycle_characteristic &&
      out.supported.phase_cycle_is_boundary && out.supported.cm_cycle_has_no_two_cell;
  form_rebase_control(foundation, first, rechart, controls);
  controls.exact = controls.equal_hull_unequal_transport &&
      controls.equal_local_population_unequal_order &&
      controls.equal_spectrum_unequal_support && controls.conjugate_rechart;
}

}  // namespace holonics::organ::intrinsic_hypergeometry_detail
