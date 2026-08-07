#pragma once

#include <holonics/codec/intrinsic_hypergeometry_face.hpp>
#include <holonics/organ/intrinsic_hypergeometry_receipt.hpp>

namespace holonics::event {

HOLONICS_CALLABLE constexpr void case_surface(
    const organ::intrinsic_phase_case_receipt& source,
    codec::intrinsic_case_surface& out) noexcept {
  out.vertices = source.vertex_count; out.edges = source.edge_count;
  out.faces = source.face_count; out.flags = source.flag_count;
  out.lcm = source.lcm; out.tours = source.tour_count;
  for (std::uint8_t row = 0; row < 4; ++row) {
    out.seams[row] = source.seam_receiver_fibers[row];
    for (std::uint8_t column = 0; column < 4; ++column) {
      out.transition_rows[row] += source.transition_population[row][column];
    }
  }
  if (source.tour_count != 0) {
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      out.section_return[slot] = source.tours[0].return_matrix[slot];
    }
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr codec::intrinsic_hypergeometry_surface
intrinsic_hypergeometry_surface(const organ::intrinsic_hypergeometry_receipt& inquiry,
    const organ::intrinsic_phase_case_receipt& changed, bool changed_sensitive) noexcept {
  codec::intrinsic_hypergeometry_surface surface{}; surface.passage = inquiry.theory.passage;
  for (std::uint8_t slot = 0; slot < organ::intrinsic_case_capacity; ++slot) {
    case_surface(inquiry.cases[slot], surface.cases[slot]);
  }
  case_surface(changed, surface.changed);
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    surface.phase_characteristic[slot] = inquiry.supported.phase_characteristic.coefficients[slot];
    surface.cm_characteristic[slot] = inquiry.supported.cm_characteristic.coefficients[slot];
  }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      surface.commutator[2U * row + column] = inquiry.local_system.commutator[row][column];
    }
  }
  surface.square_count = inquiry.supported.square_count;
  surface.incidence_exact = inquiry.theory.incidence_exact;
  surface.distributions_exact = inquiry.theory.distributions_exact;
  surface.sections_exact = inquiry.theory.sections_exact;
  surface.supports_separated = inquiry.supported.phase_cycle_is_boundary &&
      inquiry.supported.cm_cycle_has_no_two_cell;
  surface.controls_exact = inquiry.controls.exact;
  surface.changed_sensitive = changed_sensitive;
  surface.alternatives_retained = inquiry.alternatives_retained;
  return surface;
}

}  // namespace holonics::event
