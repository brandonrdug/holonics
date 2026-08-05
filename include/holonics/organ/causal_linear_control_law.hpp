#pragma once

#include <holonics/organ/causal_linear_variation_law.hpp>

namespace holonics::organ::causal_linear_detail {

HOLONICS_CALLABLE constexpr void matrix_two(causal_integer_matrix& out,
    std::int64_t a, std::int64_t b, std::int64_t c, std::int64_t d,
    std::uint64_t identity, std::uint64_t lineage) noexcept {
  set_matrix(out, 2, 2, identity, lineage);
  out.values[0][0] = a; out.values[0][1] = b;
  out.values[1][0] = c; out.values[1][1] = d;
}

HOLONICS_CALLABLE constexpr void control_spectral(const causal_linear_card& card,
    causal_control_section& out) noexcept {
  const auto lineage = card.lineage.value() + 90U;
  out.identity = exact::word{192'490}; out.lineage = exact::word{lineage};
  causal_integer_matrix identity{}; causal_integer_matrix jordan{};
  matrix_two(identity, 1, 0, 0, 1, 192'491, lineage + 1U);
  matrix_two(jordan, 1, 1, 0, 1, 192'492, lineage + 2U);
  characteristic(identity, out.identity_characteristic, 192'493);
  characteristic(jordan, out.jordan_characteristic, 192'494);
  out.identity_fixed = out.identity_characteristic.fixed_dimension;
  out.jordan_fixed = out.jordan_characteristic.fixed_dimension;
  out.equal_characteristic_unequal_fixed = same_characteristic(
      out.identity_characteristic, out.jordan_characteristic) &&
      out.identity_fixed == 2 && out.jordan_fixed == 1;
}

HOLONICS_CALLABLE constexpr void control_kernel(const causal_linear_card& card,
    causal_control_section& out) noexcept {
  const auto lineage = card.lineage.value() + 90U;
  causal_integer_matrix first{}; causal_integer_matrix second{};
  set_matrix(first, 1, 2, 192'495, lineage + 5U);
  set_matrix(second, 1, 2, 192'496, lineage + 6U);
  first.values[0][0] = 1; second.values[0][1] = 1;
  causal_matrix_analysis first_analysis{}; causal_matrix_analysis second_analysis{};
  analyze(first, first_analysis, 192'497); analyze(second, second_analysis, 192'498);
  out.unequal_kernel_placement = first_analysis.exact && second_analysis.exact &&
      first_analysis.nullity == 1 && second_analysis.nullity == 1 &&
      first_analysis.kernel[0][0].numerator == 0 &&
      first_analysis.kernel[0][1].numerator == 1 &&
      second_analysis.kernel[0][0].numerator == 1 &&
      second_analysis.kernel[0][1].numerator == 0;
}

HOLONICS_CALLABLE constexpr void control_conjugacy(const causal_linear_card& card,
    causal_control_section& out) noexcept {
  const auto lineage = card.lineage.value() + 90U;
  causal_integer_matrix left{}; causal_integer_matrix right{};
  matrix_two(left, 2, 1, 0, 3, 192'499, lineage + 9U);
  matrix_two(right, 3, 0, 1, 2, 192'500, lineage + 10U);
  causal_characteristic_receipt left_characteristic{}; causal_characteristic_receipt right_characteristic{};
  characteristic(left, left_characteristic, 192'501);
  characteristic(right, right_characteristic, 192'502);
  out.conjugacy_exact = same_characteristic(left_characteristic, right_characteristic) &&
      left.lineage != right.lineage;
}

HOLONICS_CALLABLE constexpr void control_coefficient_field(const causal_linear_card& card,
    causal_control_section& out) noexcept {
  const auto lineage = card.lineage.value() + 90U;
  causal_integer_matrix rotation{};
  matrix_two(rotation, 0, -1, 1, 0, 192'503, lineage + 13U);
  causal_characteristic_receipt rotation_characteristic{};
  characteristic(rotation, rotation_characteristic, 192'504);
  bool no_root = rotation_characteristic.exact && rotation_characteristic.degree == 2 &&
      rotation_characteristic.coefficients[0] == 1 &&
      rotation_characteristic.coefficients[1] == 0 &&
      rotation_characteristic.coefficients[2] == 1;
  for (std::int8_t value = card.eigen_min; value <= card.eigen_max; ++value) {
    bool exact = true;
    no_root = no_root && polynomial_at(rotation_characteristic, value, exact) != 0 && exact;
  }
  std::int64_t linear_square = 0; std::int64_t leading_constant = 0;
  std::int64_t four_leading_constant = 0; bool discriminant_exact = true;
  discriminant_exact = blind_integer_detail::multiply(
      rotation_characteristic.coefficients[1],
      rotation_characteristic.coefficients[1], linear_square) &&
      blind_integer_detail::multiply(rotation_characteristic.coefficients[0],
          rotation_characteristic.coefficients[2], leading_constant) &&
      blind_integer_detail::multiply(4, leading_constant, four_leading_constant) &&
      blind_integer_detail::subtract(linear_square, four_leading_constant,
          out.rational_discriminant);
  out.rational_eigenvalue_absent = no_root && discriminant_exact &&
      out.rational_discriminant < 0;
  out.gaussian_vector[0][0] = {1, 1}; out.gaussian_vector[0][1] = {0, 1};
  out.gaussian_vector[1][0] = {0, 1}; out.gaussian_vector[1][1] = {-1, 1};
  std::int64_t image[2][2]{}; std::int64_t scaled[2][2]{};
  for (std::uint8_t component = 0; component < 2; ++component) {
    image[0][component] = -out.gaussian_vector[1][component].numerator;
    image[1][component] = out.gaussian_vector[0][component].numerator;
  }
  for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
    scaled[coordinate][0] = -out.gaussian_vector[coordinate][1].numerator;
    scaled[coordinate][1] = out.gaussian_vector[coordinate][0].numerator;
  }
  out.gaussian_eigenpair_exact = true;
  for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
    for (std::uint8_t component = 0; component < 2; ++component) {
      out.gaussian_eigenpair_exact = out.gaussian_eigenpair_exact &&
          image[coordinate][component] == scaled[coordinate][component];
    }
  }
}

HOLONICS_CALLABLE constexpr void derive_control_atom(const causal_linear_card& card,
    std::uint8_t source, causal_control_section& out) noexcept {
  if (source == 0) { control_spectral(card, out); }
  else if (source == 1) { control_kernel(card, out); }
  else if (source == 2) { control_conjugacy(card, out); }
  else if (source == 3) { control_coefficient_field(card, out); }
}

HOLONICS_CALLABLE constexpr void close_controls(causal_control_section& out) noexcept {
  out.exact = out.equal_characteristic_unequal_fixed && out.unequal_kernel_placement &&
      out.conjugacy_exact && out.rational_eigenvalue_absent &&
      out.gaussian_eigenpair_exact;
}

HOLONICS_CALLABLE constexpr void derive_controls(const causal_linear_card& card,
    causal_control_section& out) noexcept {
  for (std::uint8_t source = 0; source < 4; ++source) {
    derive_control_atom(card, source, out);
  }
  close_controls(out);
}

}  // namespace holonics::organ::causal_linear_detail
