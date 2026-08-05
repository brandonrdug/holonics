#pragma once

#include <holonics/codec/algebraic_variation_face.hpp>
#include <holonics/organ/algebraic_variation_receipt.hpp>

namespace holonics::event {

[[nodiscard]] HOLONICS_CALLABLE constexpr codec::algebraic_variation_surface variation_surface(
    const organ::algebraic_variation_receipt& inquiry) noexcept {
  codec::algebraic_variation_surface surface{}; surface.passage = inquiry.theory.passage;
  for (std::uint8_t coefficient = 0; coefficient < 4; ++coefficient) {
    surface.polynomial[coefficient][0] = inquiry.mounted.coefficients[coefficient].constant;
    surface.polynomial[coefficient][1] = inquiry.mounted.coefficients[coefficient].parameter;
  }
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    surface.discriminant[slot] = inquiry.discriminant.coefficients[slot];
  }
  surface.root_count = inquiry.root_count; surface.collision_count = inquiry.collision_count;
  for (std::uint8_t root = 0; root < inquiry.root_count; ++root) {
    surface.roots[root][0] = inquiry.roots[root].root.constant;
    surface.roots[root][1] = inquiry.roots[root].root.parameter;
  }
  for (std::uint8_t collision = 0; collision < inquiry.collision_count; ++collision) {
    surface.collision_parameters[collision] = inquiry.collisions[collision].parameter.numerator;
    surface.collision_multiplicities[collision] = inquiry.collisions[collision].multiplicity;
  }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      surface.connection_numerator[row][column][0] =
          inquiry.connection.numerator[row][column].constant;
      surface.connection_numerator[row][column][1] =
          inquiry.connection.numerator[row][column].parameter;
      surface.invariant[row][column] = inquiry.invariant.selected[row][column];
      for (std::uint8_t loop = 0; loop < 3; ++loop) {
        surface.monodromy[loop][row][column] = inquiry.loops.monodromy[loop][row][column];
      }
    }
  }
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    surface.connection_pole[slot] = inquiry.connection.pole_polynomial.coefficients[slot];
    surface.scalar_second[slot] = inquiry.scalar.second[slot];
    for (std::uint8_t form = 0; form < 2; ++form) {
      surface.witness[form][slot][0] =
          inquiry.connection.witness_numerator[form][slot].constant;
      surface.witness[form][slot][1] =
          inquiry.connection.witness_numerator[form][slot].parameter;
    }
  }
  surface.connection_scale = inquiry.connection.denominator_scale;
  surface.scalar_first[0] = inquiry.scalar.first[0];
  surface.scalar_first[1] = inquiry.scalar.first[1];
  surface.scalar_zeroth = inquiry.scalar.zeroth;
  surface.series_count = inquiry.scalar.series_count;
  for (std::uint8_t slot = 0; slot < inquiry.scalar.series_count; ++slot) {
    surface.series[slot] = inquiry.scalar.series[slot];
  }
  surface.invariant_survivors = static_cast<std::uint8_t>(inquiry.invariant.discovery_survivors);
  surface.retained_candidates = inquiry.invariant.retained_count;
  surface.family_exact = inquiry.discriminant_exact && inquiry.roots_exact;
  surface.reduction_exact = inquiry.connection.symbolic_residual_zero;
  surface.connection_exact = inquiry.connection.exact;
  surface.invariant_exact = inquiry.invariant.exact;
  surface.operator_exact = inquiry.scalar.exact;
  surface.loops_exact = inquiry.loops.exact;
  surface.selection_exact = inquiry.selection.exact;
  surface.alternatives_retained = inquiry.alternatives_retained;
  return surface;
}

}  // namespace holonics::event
