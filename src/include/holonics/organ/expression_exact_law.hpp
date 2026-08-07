#pragma once

#include <holonics/organ/causal_linear_rational.hpp>
#include <holonics/organ/expression_geometry_receipt.hpp>

namespace holonics::organ::expression_exact_detail {

namespace rational = causal_linear_detail;

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::small_rational zero() noexcept {
  return {0, 1};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr exact::small_rational one() noexcept {
  return {1, 1};
}

template<std::size_t Capacity>
HOLONICS_CALLABLE constexpr void clear(
    exact::small_rational (&values)[Capacity]) noexcept {
  for (auto& value : values) { value = zero(); }
}

template<std::size_t Rows, std::size_t Columns>
HOLONICS_CALLABLE constexpr void clear(
    exact::small_rational (&values)[Rows][Columns]) noexcept {
  for (auto& row : values) { clear(row); }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    exact::small_rational left, exact::small_rational right) noexcept {
  return exact::small_rational_law::equal(left, right);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  if (!rational::rational_valid(left) || !rational::rational_valid(right)) { return false; }
  const auto first = exact::small_rational_law::gcd(left.numerator, right.denominator);
  const auto second = exact::small_rational_law::gcd(right.numerator, left.denominator);
  std::int64_t ln = 0; std::int64_t rd = 0; std::int64_t rn = 0; std::int64_t ld = 0;
  std::int64_t numerator = 0; std::int64_t denominator = 0;
  return blind_integer_detail::divide_exact(left.numerator, first, ln) &&
      blind_integer_detail::divide_exact(right.denominator, first, rd) &&
      blind_integer_detail::divide_exact(right.numerator, second, rn) &&
      blind_integer_detail::divide_exact(left.denominator, second, ld) &&
      blind_integer_detail::multiply(ln, rn, numerator) &&
      blind_integer_detail::multiply(ld, rd, denominator) &&
      rational::rational_make(numerator, denominator, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  if (!rational::rational_valid(left) || !rational::rational_valid(right)) { return false; }
  const auto divisor = exact::small_rational_law::gcd(left.denominator, right.denominator);
  std::int64_t left_scale = 0; std::int64_t right_scale = 0;
  std::int64_t first = 0; std::int64_t second = 0; std::int64_t numerator = 0;
  std::int64_t denominator = 0;
  return blind_integer_detail::divide_exact(right.denominator, divisor, left_scale) &&
      blind_integer_detail::divide_exact(left.denominator, divisor, right_scale) &&
      blind_integer_detail::multiply(left.numerator, left_scale, first) &&
      blind_integer_detail::multiply(right.numerator, right_scale, second) &&
      blind_integer_detail::add(first, second, numerator) &&
      blind_integer_detail::multiply(left.denominator, left_scale, denominator) &&
      rational::rational_make(numerator, denominator, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool negate(
    exact::small_rational value, exact::small_rational& out) noexcept {
  return rational::rational_negate(value, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool subtract(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  exact::small_rational negative{}; return negate(right, negative) && add(left, negative, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool divide(
    exact::small_rational left, exact::small_rational right,
    exact::small_rational& out) noexcept {
  if (right.numerator == 0) { return false; }
  return multiply(left, exact::small_rational_law::make(
      right.denominator, right.numerator), out);
}

HOLONICS_CALLABLE constexpr void normalize(expression_parameter_polynomial& value) noexcept {
  std::uint8_t degree = static_cast<std::uint8_t>(expression_parameter_capacity - 1U);
  while (degree != 0 && value.coefficients[degree] == 0) { --degree; }
  value.degree = degree; value.exact = true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool evaluate(
    const expression_parameter_polynomial& polynomial, exact::small_rational point,
    exact::small_rational& out) noexcept {
  if (!polynomial.exact) { return false; }
  out = zero();
  for (std::uint8_t offset = 0; offset <= polynomial.degree; ++offset) {
    const auto slot = static_cast<std::uint8_t>(polynomial.degree - offset);
    exact::small_rational product{}; exact::small_rational coefficient{};
      if (!multiply(out, point, product) ||
        !rational::rational_make(polynomial.coefficients[slot], coefficient) ||
        !add(product, coefficient, out)) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool solve(
    exact::small_rational (&matrix)[9][10], std::uint8_t size,
    exact::small_rational (&solution)[9]) noexcept {
  if (size == 0 || size > 9) { return false; }
  for (std::uint8_t column = 0; column < size; ++column) {
    std::uint8_t pivot = column;
    while (pivot < size && matrix[pivot][column].numerator == 0) { ++pivot; }
    if (pivot == size) { return false; }
    for (std::uint8_t slot = column; slot <= size; ++slot) {
      const auto held = matrix[column][slot]; matrix[column][slot] = matrix[pivot][slot];
      matrix[pivot][slot] = held;
    }
    const auto divisor = matrix[column][column];
    for (std::uint8_t slot = column; slot <= size; ++slot) {
      exact::small_rational quotient{};
      if (!divide(matrix[column][slot], divisor, quotient)) { return false; }
      matrix[column][slot] = quotient;
    }
    for (std::uint8_t row = 0; row < size; ++row) {
      if (row == column || matrix[row][column].numerator == 0) { continue; }
      const auto factor = matrix[row][column];
      for (std::uint8_t slot = column; slot <= size; ++slot) {
        exact::small_rational product{}; exact::small_rational difference{};
        if (!multiply(factor, matrix[column][slot], product) ||
            !subtract(matrix[row][slot], product, difference)) {
          return false;
        }
        matrix[row][slot] = difference;
      }
    }
  }
  for (std::uint8_t slot = 0; slot < size; ++slot) { solution[slot] = matrix[slot][size]; }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool interpolate(
    const exact::small_rational (&values)[9], std::int8_t first,
    expression_parameter_polynomial& out) noexcept {
  exact::small_rational matrix[9][10]{};
  for (std::uint8_t row = 0; row < 9; ++row) {
    const auto point = static_cast<std::int64_t>(first) + row;
    exact::small_rational power = one();
    for (std::uint8_t column = 0; column < 9; ++column) {
      matrix[row][column] = power; exact::small_rational next{};
      if (!multiply(power, {point, 1}, next)) { return false; }
      power = next;
    }
    matrix[row][9] = values[row];
  }
  exact::small_rational solution[9]{};
  if (!solve(matrix, 9, solution)) { return false; }
  for (std::uint8_t slot = 0; slot < 9; ++slot) {
    if (solution[slot].denominator != 1) { return false; }
    out.coefficients[slot] = solution[slot].numerator;
  }
  normalize(out); return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t integer_power(
    std::int64_t base, std::uint8_t exponent, bool& exact) noexcept {
  std::int64_t result = 1;
  for (std::uint8_t slot = 0; slot < exponent; ++slot) {
    std::int64_t next = 0;
    exact = exact && blind_integer_detail::multiply(result, base, next); result = next;
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_polynomial(
    const expression_parameter_polynomial& left,
    const expression_parameter_polynomial& right) noexcept {
  for (std::size_t slot = 0; slot < expression_parameter_capacity; ++slot) {
    if (left.coefficients[slot] != right.coefficients[slot]) { return false; }
  }
  return left.exact && right.exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add_scaled_affine(
    expression_parameter_polynomial& target,
    const expression_parameter_polynomial& source,
    expression_affine_coefficient scale) noexcept {
  if (!source.exact) { return false; }
  for (std::uint8_t slot = 0; slot <= source.degree; ++slot) {
    std::int64_t product = 0; std::int64_t next = 0;
    if (!blind_integer_detail::multiply(source.coefficients[slot], scale.constant, product) ||
        !blind_integer_detail::add(target.coefficients[slot], product, next)) { return false; }
    target.coefficients[slot] = next;
    if (scale.parameter != 0) {
      if (slot + 1U >= expression_parameter_capacity ||
          !blind_integer_detail::multiply(source.coefficients[slot], scale.parameter, product) ||
          !blind_integer_detail::add(target.coefficients[slot + 1U], product, next)) {
        return false;
      }
      target.coefficients[slot + 1U] = next;
    }
  }
  normalize(target); return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool scale_polynomial(
    const expression_parameter_polynomial& source, std::int64_t scale,
    expression_parameter_polynomial& out) noexcept {
  if (!source.exact) { return false; }
  for (std::uint8_t slot = 0; slot <= source.degree; ++slot) {
    if (!blind_integer_detail::multiply(source.coefficients[slot], scale,
            out.coefficients[slot])) { return false; }
  }
  normalize(out); return true;
}

}  // namespace holonics::organ::expression_exact_detail
