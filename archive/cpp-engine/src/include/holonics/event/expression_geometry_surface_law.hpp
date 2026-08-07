#pragma once

#include <holonics/codec/expression_geometry_face.hpp>
#include <holonics/organ/expression_geometry_receipt.hpp>

namespace holonics::event {

[[nodiscard]] HOLONICS_CALLABLE constexpr codec::expression_geometry_surface
expression_geometry_surface(const organ::expression_geometry_receipt& inquiry,
    const organ::expression_changed_receipt& changed, bool changed_sensitive) noexcept {
  codec::expression_geometry_surface out{}; out.passage = inquiry.theory.passage;
  for (std::uint8_t slot = 0; slot < 6; ++slot) {
    out.resultant[slot] = inquiry.presentations[0].ideal.resultant.coefficients[slot];
    out.changed_resultant[slot] = changed.presentations[0].ideal.resultant.coefficients[slot];
  }
  for (std::uint8_t x = 0; x < 4; ++x) {
    for (std::uint8_t t = 0; t < 21; ++t) {
      out.bezout_f[x][t] = inquiry.presentations[0].ideal.bezout_f[x].coefficients[t];
    }
  }
  for (std::uint8_t x = 0; x < 5; ++x) {
    for (std::uint8_t t = 0; t < 21; ++t) {
      out.bezout_fx[x][t] = inquiry.presentations[0].ideal.bezout_fx[x].coefficients[t];
    }
  }
  for (std::uint8_t basis = 0; basis < 4; ++basis) {
    for (std::uint8_t x = 0; x < 4; ++x) {
      for (std::uint8_t t = 0; t < 21; ++t) {
        out.reduction_p[basis][x][t] =
            inquiry.presentations[0].connection.reduction_p[basis][x].coefficients[t];
      }
    }
    for (std::uint8_t x = 0; x < 5; ++x) {
      for (std::uint8_t t = 0; t < 21; ++t) {
        out.reduction_q[basis][x][t] =
            inquiry.presentations[0].connection.reduction_q[basis][x].coefficients[t];
      }
    }
  }
  out.scalar[0] = inquiry.presentations[0].scalar.coefficients[4].coefficients[0];
  out.scalar[1] = inquiry.presentations[0].scalar.coefficients[4].coefficients[5];
  out.scalar[2] = inquiry.presentations[0].scalar.coefficients[3].coefficients[4];
  out.scalar[3] = inquiry.presentations[0].scalar.coefficients[2].coefficients[3];
  out.scalar[4] = inquiry.presentations[0].scalar.coefficients[1].coefficients[2];
  out.scalar[5] = inquiry.presentations[0].scalar.coefficients[0].coefficients[1];
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    out.finite_indicial[slot] = inquiry.presentations[0].indicial.finite_coefficients[slot];
    out.infinity_indicial[slot] = inquiry.presentations[0].indicial.infinity_coefficients[slot];
    out.residue_entry[slot] = inquiry.presentations[0].residue.matrix[0][0].coefficients[slot];
  }
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      for (std::uint8_t degree = 0; degree < 5; ++degree) {
        out.residue[row][column][degree] =
            inquiry.presentations[0].residue.matrix[row][column].coefficients[degree];
      }
    }
  }
  for (std::uint8_t front = 0; front < 4; ++front) {
    for (std::uint8_t slot = 0; slot < 11; ++slot) {
      out.series[front][slot] = inquiry.presentations[0].scalar.series[front][slot];
    }
  }
  out.changed_series = changed.presentations[0].scalar.series[0][5];
  out.rational_shift = inquiry.rational_rechart.x_shift;
  out.gaussian_x_scale = inquiry.gaussian_rechart.x_scale;
  out.gaussian_y_square = inquiry.gaussian_rechart.y_square;
  out.singular_count = inquiry.presentations[0].ideal.geometric_singular_count;
  out.family_constant = inquiry.presentations[0].ideal.constant_parameter;
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    out.fiber_members[slot] = inquiry.invariant_fiber.members[slot];
  }
  for (std::uint8_t slot = 0; slot <
      inquiry.presentations[1].mounted.term_count; ++slot) {
    const auto& term = inquiry.presentations[1].mounted.terms[slot];
    if (term.y_power != 0) { continue; }
    if (term.parameter_power == 0) { out.translated_constant[term.x_power] += term.coefficient; }
    else { out.translated_parameter[term.x_power] += term.coefficient; }
  }
  out.ideals_exact = inquiry.theory.ideals_exact;
  out.differential_exact = inquiry.theory.differential_exact;
  out.residue_exact = inquiry.presentations[0].residue.exact;
  out.fibers_exact = inquiry.theory.fibers_exact;
  out.changed_sensitive = changed_sensitive;
  out.alternatives_retained = inquiry.alternatives_retained; return out;
}

}  // namespace holonics::event
