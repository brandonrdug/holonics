#pragma once

#include <holonics/organ/hodge_product_law.hpp>

namespace holonics::organ::hodge_correspondence_detail {

struct x_polynomial final {
  parameter_polynomial coefficients[7]{};
  std::uint8_t degree{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial constant(
    std::int64_t value) noexcept {
  parameter_polynomial out{}; out.coefficients[0] = value;
  variation_polynomial_detail::normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial parameter() noexcept {
  parameter_polynomial out{}; out.coefficients[1] = 1;
  variation_polynomial_detail::normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr parameter_polynomial root(
    affine_integer_coefficient value) noexcept {
  return variation_polynomial_detail::affine(value);
}

HOLONICS_CALLABLE constexpr void normalize(x_polynomial& value) noexcept {
  std::uint8_t degree = 6;
  while (degree != 0 && variation_polynomial_detail::zero(value.coefficients[degree])) {
    --degree;
  }
  value.degree = degree;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial scalar(
    parameter_polynomial value) noexcept {
  x_polynomial out{}; out.coefficients[0] = value; normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial x() noexcept {
  x_polynomial out{}; out.coefficients[1] = constant(1); normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial add(
    const x_polynomial& left, const x_polynomial& right) noexcept {
  x_polynomial out{};
  for (std::uint8_t slot = 0; slot < 7; ++slot) {
    out.coefficients[slot] = variation_polynomial_detail::add(
        left.coefficients[slot], right.coefficients[slot]);
  }
  normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial negate(
    const x_polynomial& value) noexcept {
  x_polynomial out{};
  for (std::uint8_t slot = 0; slot < 7; ++slot) {
    out.coefficients[slot] = variation_polynomial_detail::scale(value.coefficients[slot], -1);
  }
  normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial subtract(
    const x_polynomial& left, const x_polynomial& right) noexcept {
  return add(left, negate(right));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial multiply(
    const x_polynomial& left, const x_polynomial& right) noexcept {
  x_polynomial out{};
  for (std::uint8_t row = 0; row <= left.degree; ++row) {
    for (std::uint8_t column = 0; column <= right.degree; ++column) {
      const auto target = static_cast<std::uint8_t>(row + column);
      if (target < 7) { out.coefficients[target] = variation_polynomial_detail::add(
          out.coefficients[target], variation_polynomial_detail::multiply(
              left.coefficients[row], right.coefficients[column])); }
    }
  }
  normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial scale(
    const x_polynomial& value, parameter_polynomial factor) noexcept {
  x_polynomial out{};
  for (std::uint8_t slot = 0; slot <= value.degree; ++slot) {
    out.coefficients[slot] = variation_polynomial_detail::multiply(
        value.coefficients[slot], factor);
  }
  normalize(out); return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const x_polynomial& left, const x_polynomial& right) noexcept {
  for (std::uint8_t slot = 0; slot < 7; ++slot) {
    if (!variation_polynomial_detail::equal(left.coefficients[slot],
        right.coefficients[slot])) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void graph_class(const std::int64_t (&matrix)[2][2],
    std::int64_t (&out)[6]) noexcept {
  const auto determinant = matrix[0][0] * matrix[1][1] -
      matrix[0][1] * matrix[1][0];
  out[0] = 1; out[1] = determinant; out[2] = matrix[0][1];
  out[3] = matrix[1][1]; out[4] = -matrix[0][0]; out[5] = -matrix[1][0];
}

[[nodiscard]] HOLONICS_CALLABLE constexpr x_polynomial family_polynomial() noexcept {
  const auto xv = x(); const auto one = scalar(constant(1));
  const auto zv = scalar(parameter());
  return multiply(multiply(xv, subtract(xv, one)), subtract(xv, zv));
}

HOLONICS_CALLABLE constexpr void copy_map(const x_polynomial& numerator,
    const x_polynomial& denominator, hodge_translation_receipt& out) noexcept {
  for (std::uint8_t slot = 0; slot < 2; ++slot) {
    out.x_numerator[slot] = numerator.coefficients[slot];
    out.x_denominator[slot] = denominator.coefficients[slot];
  }
}

HOLONICS_CALLABLE constexpr void derive_translation(const hodge_factor_receipt& factor,
    std::uint8_t slot, hodge_translation_receipt& out) noexcept {
  out.identity = exact::word{195'500U + slot};
  out.lineage = exact::word{factor.lineage.value() + slot + 32U}; out.support = slot;
  constexpr std::int64_t identity[2][2]{{1,0},{0,1}};
  graph_class(identity, out.graph_class); out.h1_identity = true;
  if (slot == 0) {
    out.x_numerator[1] = constant(1); out.x_denominator[0] = constant(1);
    out.y_scale = constant(1); out.identity_map = true; out.curve_identity = true;
    out.involution = true; out.differential_pullback_identity = true;
    out.distinct_support = true; out.exact = true; return;
  }
  const std::uint8_t root_slot = static_cast<std::uint8_t>(slot - 1U);
  const std::uint8_t first[3]{1,0,0}; const std::uint8_t second[3]{2,2,1};
  out.root = root(factor.roots[root_slot].root);
  out.other_first = root(factor.roots[first[root_slot]].root);
  out.other_second = root(factor.roots[second[root_slot]].root);
  const auto first_difference = variation_polynomial_detail::subtract(
      out.root, out.other_first);
  const auto second_difference = variation_polynomial_detail::subtract(
      out.root, out.other_second);
  out.kappa = variation_polynomial_detail::multiply(first_difference, second_difference);
  const auto denominator = subtract(x(), scalar(out.root));
  const auto numerator = add(scale(denominator, out.root), scalar(out.kappa));
  out.y_scale = variation_polynomial_detail::scale(out.kappa, -1); copy_map(numerator, denominator, out);
  const auto curve = family_polynomial();
  const auto left = scale(curve, variation_polynomial_detail::multiply(out.kappa, out.kappa));
  const auto z_denominator = scale(denominator, parameter());
  const auto right = multiply(multiply(multiply(denominator, numerator),
      subtract(numerator, denominator)), subtract(numerator, z_denominator));
  out.curve_identity = equal(left, right);
  const auto derivative_numerator = scalar(numerator.coefficients[1]);
  const auto derivative_denominator = scalar(denominator.coefficients[1]);
  const auto derivative = subtract(multiply(derivative_numerator, denominator),
      multiply(numerator, derivative_denominator));
  out.differential_pullback_identity = equal(derivative, scalar(out.y_scale));
  out.involution = !variation_polynomial_detail::zero(out.kappa) && out.curve_identity;
  out.distinct_support = true; out.exact = out.curve_identity && out.involution &&
      out.differential_pullback_identity;
}

}  // namespace holonics::organ::hodge_correspondence_detail
