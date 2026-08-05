#pragma once

#include <holonics/organ/variation_reduction_law.hpp>

namespace holonics::organ::variation_connection_detail {

namespace rational = exact::small_rational_law;
namespace polynomial = variation_polynomial_detail;
namespace reduction = variation_reduction_detail;

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::small_rational affine_value(
    affine_integer_coefficient coefficient, exact::small_rational parameter) noexcept {
  return reduction::affine_value(coefficient, parameter);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial pole_polynomial(
    const algebraic_variation_receipt& out) noexcept {
  parameter_polynomial pole{}; pole.coefficients[0] = 1; polynomial::normalize(pole);
  for (std::uint8_t collision = 0; collision < out.collision_count; ++collision) {
    const auto parameter = out.collisions[collision].parameter;
    if (parameter.denominator != 1) { continue; }
    pole = polynomial::multiply(pole,
        polynomial::affine({-parameter.numerator, 1}));
  }
  const auto midpoint = polynomial::evaluate(pole, rational::make(1, 2));
  if (midpoint.numerator < 0) { pole = polynomial::scale(pole, -1); }
  return pole;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool fit_affine(
    const algebraic_variation_receipt& out, std::uint8_t row, std::uint8_t column,
    std::int64_t scale, affine_integer_coefficient& fitted) noexcept {
  std::uint8_t first = 0; std::uint8_t second = 1;
  while (second < out.mounted.discovery_count && !out.samples[second].regular) { ++second; }
  if (!out.samples[first].regular || second == out.mounted.discovery_count) { return false; }
  const auto value = [&](std::uint8_t sample) constexpr {
    return rational::multiply(rational::make(scale), rational::multiply(
        polynomial::evaluate(out.connection.pole_polynomial, out.samples[sample].parameter),
        out.samples[sample].connection[row][column]));
  };
  const auto slope = rational::divide(rational::subtract(value(second), value(first)),
      rational::subtract(out.samples[second].parameter, out.samples[first].parameter));
  const auto intercept = rational::subtract(value(first),
      rational::multiply(slope, out.samples[first].parameter));
  if (slope.denominator != 1 || intercept.denominator != 1) { return false; }
  fitted = {intercept.numerator, slope.numerator};
  for (std::uint8_t sample = 0; sample < out.mounted.discovery_count; ++sample) {
    if (!out.samples[sample].regular || !rational::equal(value(sample),
        affine_value(fitted, out.samples[sample].parameter))) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool fit_witness(
    const algebraic_variation_receipt& out, std::uint8_t form, std::uint8_t slot,
    affine_integer_coefficient& fitted) noexcept {
  std::uint8_t first = 0; std::uint8_t second = 1;
  const auto value = [&](std::uint8_t sample) constexpr {
    return rational::multiply(polynomial::evaluate(out.connection.pole_polynomial,
        out.samples[sample].parameter), out.samples[sample].reductions[form].witness[slot]);
  };
  const auto slope = rational::divide(rational::subtract(value(second), value(first)),
      rational::subtract(out.samples[second].parameter, out.samples[first].parameter));
  const auto intercept = rational::subtract(value(first),
      rational::multiply(slope, out.samples[first].parameter));
  if (slope.denominator != 1 || intercept.denominator != 1) { return false; }
  fitted = {intercept.numerator, slope.numerator};
  for (std::uint8_t sample = 0; sample < out.mounted.discovery_count; ++sample) {
    if (!rational::equal(value(sample), affine_value(fitted,
        out.samples[sample].parameter))) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool symbolic_residual(
    const algebraic_variation_receipt& out, std::uint8_t form) noexcept {
  const auto scale = out.connection.denominator_scale;
  const auto denominator = polynomial::scale(out.connection.pole_polynomial, scale);
  parameter_polynomial f[4]{}; parameter_polynomial fx[3]{};
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    f[slot] = polynomial::affine(out.mounted.coefficients[slot]);
  }
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    fx[slot] = polynomial::scale(f[slot + 1U], slot + 1U);
  }
  for (std::uint8_t row = 0; row < 5; ++row) {
    parameter_polynomial residual{}; polynomial::normalize(residual);
    if (row >= form && row - form < 4) {
      residual = polynomial::add(residual, polynomial::scale(denominator,
          -out.mounted.coefficients[row - form].parameter));
    }
    if (row < 4) { residual = polynomial::add(residual, polynomial::scale(
        polynomial::multiply(polynomial::affine(out.connection.numerator[form][0]),
            f[row]), -2)); }
    if (row > 0 && row - 1U < 4) { residual = polynomial::add(residual,
        polynomial::scale(polynomial::multiply(
            polynomial::affine(out.connection.numerator[form][1]), f[row - 1U]), -2)); }
    for (std::uint8_t witness = 0; witness < 3; ++witness) {
      const auto g = polynomial::affine(out.connection.witness_numerator[form][witness]);
      if (witness != 0 && row + 1U >= witness && row + 1U - witness < 4) {
        residual = polynomial::add(residual, polynomial::scale(
            polynomial::multiply(g, f[row + 1U - witness]),
            -2 * scale * witness));
      }
      if (row >= witness && row - witness < 3) {
        residual = polynomial::add(residual, polynomial::scale(
            polynomial::multiply(g, fx[row - witness]), scale));
      }
    }
    if (!polynomial::zero(residual)) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void derive_global_connection(
    algebraic_variation_receipt& out) noexcept {
  out.connection.pole_polynomial = pole_polynomial(out);
  bool fitted = false;
  for (std::int64_t scale = 1; scale <= 8 && !fitted; ++scale) {
    fitted = true;
    for (std::uint8_t row = 0; row < 2; ++row) {
      for (std::uint8_t column = 0; column < 2; ++column) {
        fitted = fit_affine(out, row, column, scale,
            out.connection.numerator[row][column]) && fitted;
      }
    }
    if (fitted) { out.connection.denominator_scale = scale; }
  }
  bool witnesses = fitted;
  for (std::uint8_t form = 0; form < 2; ++form) {
    for (std::uint8_t slot = 0; slot < 3; ++slot) {
      witnesses = fit_witness(out, form, slot,
          out.connection.witness_numerator[form][slot]) && witnesses;
    }
  }
  out.connection.holdouts_exact = fitted;
  for (std::uint8_t sample = out.mounted.discovery_count;
      sample < out.mounted.sample_count; ++sample) {
    const auto denominator = rational::multiply(rational::make(
        out.connection.denominator_scale), polynomial::evaluate(
        out.connection.pole_polynomial, out.samples[sample].parameter));
    for (std::uint8_t row = 0; row < 2; ++row) {
      for (std::uint8_t column = 0; column < 2; ++column) {
        out.connection.holdouts_exact = out.connection.holdouts_exact && rational::equal(
            out.samples[sample].connection[row][column], rational::divide(
            affine_value(out.connection.numerator[row][column],
                out.samples[sample].parameter), denominator));
      }
    }
  }
  out.connection.symbolic_residual_zero = witnesses && symbolic_residual(out, 0) &&
      symbolic_residual(out, 1);
  out.connection.pole_support_matches_discriminant = out.collision_count == 2 &&
      out.discriminant.degree == 4 && out.connection.pole_polynomial.degree == 2;
  out.connection.identity = exact::word{191'500};
  out.connection.lineage = exact::word{out.mounted.lineage.value() + 96U};
  out.connection.discovery_only = true;
  out.connection.exact = out.connection.holdouts_exact &&
      out.connection.symbolic_residual_zero &&
      out.connection.pole_support_matches_discriminant;
}

HOLONICS_CALLABLE constexpr void derive_connection(algebraic_variation_receipt& out) noexcept {
  if (out.obstruction != variation_obstruction::none) { return; }
  reduction::derive_samples(out); derive_global_connection(out);
  if (!out.connection.exact) { out.obstruction = variation_obstruction::connection_refused; }
}

}  // namespace holonics::organ::variation_connection_detail
