#pragma once

#include <holonics/organ/expression_series_law.hpp>

namespace holonics::organ::expression_residue_detail {

using value = expression_algebraic_value;

HOLONICS_CALLABLE constexpr void clear(value& out) noexcept {
  expression_exact_detail::clear(out.coefficients);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add(
    const value& left, const value& right, value& out) noexcept {
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (!causal_linear_detail::rational_add(
            left.coefficients[slot], right.coefficients[slot], out.coefficients[slot])) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool negate(const value& source, value& out) noexcept {
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (!causal_linear_detail::rational_negate(source.coefficients[slot],
            out.coefficients[slot])) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool subtract(
    const value& left, const value& right, value& out) noexcept {
  value negative{}; return negate(right, negative) && add(left, negative, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(
    const value& left, const value& right, std::int64_t relation_constant,
    value& out) noexcept {
  exact::small_rational work[9]{};
  expression_exact_detail::clear(work);
  for (std::uint8_t l = 0; l < 5; ++l) {
    for (std::uint8_t r = 0; r < 5; ++r) {
      exact::small_rational product{}; exact::small_rational next{};
      if (!causal_linear_detail::rational_multiply(left.coefficients[l],
              right.coefficients[r], product) ||
          !causal_linear_detail::rational_add(work[l + r], product, next)) { return false; }
      work[l + r] = next;
    }
  }
  const auto relation = exact::small_rational_law::make(relation_constant, 4);
  for (std::uint8_t offset = 0; offset < 4; ++offset) {
    const auto degree = static_cast<std::uint8_t>(8U - offset);
    exact::small_rational product{}; exact::small_rational next{};
    if (!causal_linear_detail::rational_multiply(work[degree], relation, product) ||
        !causal_linear_detail::rational_add(work[degree - 5U], product, next)) { return false; }
    work[degree - 5U] = next;
  }
  for (std::uint8_t slot = 0; slot < 5; ++slot) { out.coefficients[slot] = work[slot]; }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool scale(
    const value& source, exact::small_rational factor, value& out) noexcept {
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (!causal_linear_detail::rational_multiply(
            source.coefficients[slot], factor, out.coefficients[slot])) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool zero(const value& source) noexcept {
  for (const auto coefficient : source.coefficients) {
    if (coefficient.numerator != 0) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool parameter_value(
    const expression_parameter_polynomial& polynomial, std::int64_t relation_constant,
    value& out) noexcept {
  clear(out); value parameter{}; clear(parameter); parameter.coefficients[4] = {5,1};
  for (std::uint8_t offset = 0; offset <= polynomial.degree; ++offset) {
    const auto slot = static_cast<std::uint8_t>(polynomial.degree - offset);
    value product{}; value coefficient{}; value next{}; clear(coefficient);
    coefficient.coefficients[0] = {polynomial.coefficients[slot],1};
    if (!multiply(out, parameter, relation_constant, product) ||
        !add(product, coefficient, next)) { return false; }
    out = next;
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool inverse(
    const value& source, std::int64_t relation_constant, value& out) noexcept {
  exact::small_rational system[9][10]{};
  expression_exact_detail::clear(system);
  for (std::uint8_t column = 0; column < 5; ++column) {
    value basis{}; clear(basis); basis.coefficients[column] = {1,1}; value product{};
    if (!multiply(source, basis, relation_constant, product)) { return false; }
    for (std::uint8_t row = 0; row < 5; ++row) {
      system[row][column] = product.coefficients[row];
    }
  }
  system[0][5] = {1,1}; exact::small_rational solution[9]{};
  if (!expression_exact_detail::solve(system, 5, solution)) { return false; }
  for (std::uint8_t slot = 0; slot < 5; ++slot) { out.coefficients[slot] = solution[slot]; }
  value check{}; return multiply(source, out, relation_constant, check) &&
      expression_exact_detail::equal(check.coefficients[0], {1,1}) &&
      check.coefficients[1].numerator == 0 && check.coefficients[2].numerator == 0 &&
      check.coefficients[3].numerator == 0 && check.coefficients[4].numerator == 0;
}

HOLONICS_CALLABLE constexpr void derive(expression_presentation_receipt& out) noexcept {
  auto& receipt = out.residue; const auto constant = out.ideal.constant_parameter;
  bool exact = out.connection.exact && constant != 0; receipt.relation_constant = constant;
  expression_parameter_polynomial derivative{};
  for (std::uint8_t slot = 1; slot <= out.ideal.resultant.degree; ++slot) {
    exact = exact && blind_integer_detail::multiply(out.ideal.resultant.coefficients[slot], slot,
        derivative.coefficients[slot - 1U]);
  }
  expression_exact_detail::normalize(derivative);
  value derivative_value{}; value doubled{}; value inverse_derivative{};
  exact = exact && parameter_value(derivative, constant, derivative_value) &&
      scale(derivative_value, {2,1}, doubled) && inverse(doubled, constant, inverse_derivative);
  for (std::uint8_t row = 0; row < 4 && exact; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      value numerator{};
      exact = parameter_value(out.connection.numerator[row][column], constant, numerator) &&
          multiply(numerator, inverse_derivative, constant, receipt.matrix[row][column]);
    }
  }
  receipt.nonzero = !zero(receipt.matrix[0][0]); receipt.all_two_minors_zero = exact;
  for (std::uint8_t r0 = 0; r0 < 4; ++r0) {
    for (std::uint8_t r1 = static_cast<std::uint8_t>(r0 + 1U); r1 < 4; ++r1) {
      for (std::uint8_t c0 = 0; c0 < 4; ++c0) {
        for (std::uint8_t c1 = static_cast<std::uint8_t>(c0 + 1U); c1 < 4; ++c1) {
          value left{}; value right{}; value minor{};
          exact = exact && multiply(receipt.matrix[r0][c0], receipt.matrix[r1][c1],
              constant, left) && multiply(receipt.matrix[r0][c1], receipt.matrix[r1][c0],
              constant, right) && subtract(left, right, minor);
          receipt.all_two_minors_zero = receipt.all_two_minors_zero && zero(minor);
        }
      }
    }
  }
  receipt.square_zero = exact;
  for (std::uint8_t row = 0; row < 4; ++row) {
    for (std::uint8_t column = 0; column < 4; ++column) {
      value sum{}; clear(sum);
      for (std::uint8_t inner = 0; inner < 4; ++inner) {
        value product{}; value next{};
        exact = exact && multiply(receipt.matrix[row][inner], receipt.matrix[inner][column],
            constant, product) && add(sum, product, next); sum = next;
      }
      receipt.square_zero = receipt.square_zero && zero(sum);
    }
  }
  receipt.rank_one = receipt.nonzero && receipt.all_two_minors_zero;
  receipt.logarithmic_channel = receipt.rank_one && receipt.square_zero &&
      out.indicial.repeated_finite_root;
  receipt.identity = exact::word{194'740}; receipt.lineage = exact::word{out.lineage.value() + 512U};
  receipt.exact = exact && receipt.rank_one && receipt.square_zero && receipt.logarithmic_channel;
  out.exact = out.exact && receipt.exact;
}

}  // namespace holonics::organ::expression_residue_detail
