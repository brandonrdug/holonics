#pragma once

#include <holonics/organ/variation_polynomial_law.hpp>

namespace holonics::organ::variation_reduction_detail {

namespace rational = exact::small_rational_law;
namespace polynomial = variation_polynomial_detail;

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::small_rational affine_value(
    affine_integer_coefficient coefficient, exact::small_rational parameter) noexcept {
  return rational::add(rational::make(coefficient.constant),
      rational::multiply(rational::make(coefficient.parameter), parameter));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool solve_reduction(
    const algebraic_variation_card& card, exact::small_rational parameter,
    std::uint8_t power, differential_reduction_receipt& out) noexcept {
  exact::small_rational f[4]{}; exact::small_rational derivative[3]{};
  for (std::uint8_t slot = 0; slot < 4; ++slot) {
    f[slot] = affine_value(card.coefficients[slot], parameter);
    if (slot < 3) { derivative[slot] = rational::multiply(rational::make(slot + 1U),
        affine_value(card.coefficients[slot + 1U], parameter)); }
  }
  exact::small_rational matrix[5][6]{};
  for (std::uint8_t row = 0; row < 5; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      matrix[row][column] = rational::make(0);
    }
    if (row < 4) { matrix[row][0] = rational::multiply(rational::make(-2), f[row]); }
    if (row > 0 && row - 1U < 4) {
      matrix[row][1] = rational::multiply(rational::make(-2), f[row - 1U]);
    }
    for (std::uint8_t witness = 0; witness < 3; ++witness) {
      auto coefficient = rational::make(0);
      if (witness != 0 && row + 1U >= witness && row + 1U - witness < 4) {
        coefficient = rational::add(coefficient, rational::multiply(
            rational::make(-2 * witness), f[row + 1U - witness]));
      }
      if (row >= witness && row - witness < 3) {
        coefficient = rational::add(coefficient, derivative[row - witness]);
      }
      matrix[row][2U + witness] = coefficient;
    }
    if (row >= power && row - power < 4) {
      matrix[row][5] = rational::make(card.coefficients[row - power].parameter);
    }
  }
  exact::small_rational original[5][6]{};
  for (std::uint8_t row = 0; row < 5; ++row) {
    for (std::uint8_t column = 0; column < 6; ++column) {
      original[row][column] = matrix[row][column];
    }
  }
  for (std::uint8_t column = 0; column < 5; ++column) {
    std::uint8_t pivot = column;
    while (pivot < 5 && matrix[pivot][column].numerator == 0) { ++pivot; }
    if (pivot == 5) { return false; }
    if (pivot != column) {
      for (std::uint8_t slot = column; slot < 6; ++slot) {
        const auto held = matrix[column][slot]; matrix[column][slot] = matrix[pivot][slot];
        matrix[pivot][slot] = held;
      }
    }
    const auto divisor = matrix[column][column];
    for (std::uint8_t slot = column; slot < 6; ++slot) {
      matrix[column][slot] = rational::divide(matrix[column][slot], divisor);
    }
    for (std::uint8_t row = 0; row < 5; ++row) {
      if (row == column) { continue; }
      const auto factor = matrix[row][column];
      for (std::uint8_t slot = column; slot < 6; ++slot) {
        matrix[row][slot] = rational::subtract(matrix[row][slot],
            rational::multiply(factor, matrix[column][slot]));
      }
    }
  }
  out.connection[0] = matrix[0][5]; out.connection[1] = matrix[1][5];
  for (std::uint8_t slot = 0; slot < 3; ++slot) { out.witness[slot] = matrix[2U + slot][5]; }
  out.coefficient_residual_zero = true;
  for (std::uint8_t row = 0; row < 5; ++row) {
    auto residual = rational::make(0);
    for (std::uint8_t column = 0; column < 5; ++column) {
      residual = rational::add(residual,
          rational::multiply(original[row][column], matrix[column][5]));
    }
    out.coefficient_residual_zero = out.coefficient_residual_zero &&
        rational::equal(residual, original[row][5]);
  }
  out.exact = out.coefficient_residual_zero; return out.exact;
}

HOLONICS_CALLABLE constexpr void derive_samples(algebraic_variation_receipt& out) noexcept {
  const auto& card = out.mounted;
  for (std::uint8_t sample = 0; sample < card.sample_count; ++sample) {
    auto& returned = out.samples[sample]; returned.parameter = card.samples[sample];
    returned.identity = exact::word{191'440U + sample};
    returned.lineage = exact::word{card.lineage.value() + 64U + sample};
    returned.discovery = sample < card.discovery_count;
    returned.holdout = sample >= card.discovery_count;
    returned.discriminant = polynomial::evaluate(out.discriminant, returned.parameter);
    returned.regular = returned.discriminant.numerator != 0;
    returned.singular = !returned.regular;
    if (!returned.regular) { continue; }
    bool exact = true;
    for (std::uint8_t form = 0; form < 2; ++form) {
      returned.reductions[form].identity = exact::word{191'480U + sample * 2U + form};
      returned.reductions[form].lineage = exact::word{returned.lineage.value() + form + 1U};
      exact = solve_reduction(card, returned.parameter, form, returned.reductions[form]) && exact;
      for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
        returned.connection[form][coordinate] =
            returned.reductions[form].connection[coordinate];
      }
    }
    returned.exact = exact;
  }
}

}  // namespace holonics::organ::variation_reduction_detail
