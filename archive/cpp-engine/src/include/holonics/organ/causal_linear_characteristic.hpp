#pragma once

#include <holonics/organ/causal_linear_matrix.hpp>

namespace holonics::organ::causal_linear_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool square_product(
    const causal_integer_matrix& left, const causal_integer_matrix& right,
    causal_integer_matrix& out, std::uint64_t identity) noexcept {
  return left.rows == left.columns && right.rows == right.columns &&
      left.rows == right.rows && multiply(left, right, out, identity);
}

HOLONICS_CALLABLE constexpr void characteristic(const causal_integer_matrix& source,
    causal_characteristic_receipt& out, std::uint64_t identity) noexcept {
  out.identity = exact::word{identity};
  out.lineage = exact::word{source.lineage.value() + 2U};
  if (!valid_shape(source) || source.rows != source.columns ||
      source.rows > causal_square_degree) { return; }
  causal_integer_matrix power = source;
  bool exact = true;
  for (std::uint8_t order = 0; order < source.rows; ++order) {
    std::int64_t trace = 0;
    for (std::uint8_t diagonal = 0; diagonal < source.rows; ++diagonal) {
      std::int64_t next = 0;
      exact = exact && blind_integer_detail::add(
          trace, power.values[diagonal][diagonal], next);
      trace = next;
    }
    out.traces[order] = trace;
    if (order + 1U < source.rows) {
      causal_integer_matrix next{};
      exact = exact && square_product(power, source, next, identity + order + 1U);
      power = next;
    }
  }
  out.coefficients[0] = 1;
  for (std::uint8_t degree = 1; degree <= source.rows; ++degree) {
    std::int64_t sum = 0;
    for (std::uint8_t index = 1; index <= degree; ++index) {
      std::int64_t product = 0; std::int64_t next = 0;
      exact = exact && blind_integer_detail::multiply(
          out.coefficients[degree - index], out.traces[index - 1U], product) &&
          blind_integer_detail::add(sum, product, next);
      sum = next;
    }
    std::int64_t negative_sum = 0;
    exact = exact && checked_negate(sum, negative_sum) &&
        blind_integer_detail::divide_exact(negative_sum,
            static_cast<std::int64_t>(degree), out.coefficients[degree]);
  }
  causal_integer_matrix fixed = source;
  for (std::uint8_t diagonal = 0; diagonal < source.rows; ++diagonal) {
    exact = exact && blind_integer_detail::subtract(
        fixed.values[diagonal][diagonal], 1, fixed.values[diagonal][diagonal]);
  }
  causal_matrix_analysis analysis{}; analyze(fixed, analysis, identity + 80U);
  out.degree = source.rows; out.fixed_dimension = analysis.nullity;
  out.exact = exact && analysis.exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_characteristic(
    const causal_characteristic_receipt& left,
    const causal_characteristic_receipt& right) noexcept {
  if (!left.exact || !right.exact || left.degree != right.degree) { return false; }
  for (std::uint8_t slot = 0; slot <= left.degree; ++slot) {
    if (left.coefficients[slot] != right.coefficients[slot]) { return false; }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void kronecker(const std::int64_t left[2][2],
    const std::int64_t right[2][2], causal_integer_matrix& out,
    std::uint64_t identity, std::uint64_t lineage) noexcept {
  set_matrix(out, 4, 4, identity, lineage); bool exact = out.exact;
  for (std::uint8_t lr = 0; lr < 2; ++lr) {
    for (std::uint8_t lc = 0; lc < 2; ++lc) {
      for (std::uint8_t rr = 0; rr < 2; ++rr) {
        for (std::uint8_t rc = 0; rc < 2; ++rc) {
          exact = exact && blind_integer_detail::multiply(left[lr][lc], right[rr][rc],
              out.values[static_cast<std::uint8_t>(2U * lr + rr)]
                  [static_cast<std::uint8_t>(2U * lc + rc)]);
        }
      }
    }
  }
  out.exact = exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t determinant_two(
    const std::int64_t value[2][2], bool& exact) noexcept {
  std::int64_t left = 0; std::int64_t right = 0; std::int64_t result = 0;
  exact = exact && blind_integer_detail::multiply(value[0][0], value[1][1], left) &&
      blind_integer_detail::multiply(value[0][1], value[1][0], right) &&
      blind_integer_detail::subtract(left, right, result);
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool preserves_form(
    const std::int64_t matrix[2][2], const std::int64_t form[2][2]) noexcept {
  std::int64_t first[2][2]{}; std::int64_t result[2][2]{}; bool exact = true;
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        std::int64_t product = 0; std::int64_t next = 0;
        exact = exact && blind_integer_detail::multiply(
            form[row][inner], matrix[inner][column], product) &&
            blind_integer_detail::add(first[row][column], product, next);
        first[row][column] = next;
      }
    }
  }
  for (std::uint8_t row = 0; row < 2; ++row) {
    for (std::uint8_t column = 0; column < 2; ++column) {
      for (std::uint8_t inner = 0; inner < 2; ++inner) {
        std::int64_t product = 0; std::int64_t next = 0;
        exact = exact && blind_integer_detail::multiply(
            matrix[inner][row], first[inner][column], product) &&
            blind_integer_detail::add(result[row][column], product, next);
        result[row][column] = next;
      }
      exact = exact && result[row][column] == form[row][column];
    }
  }
  return exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t polynomial_at(
    const causal_characteristic_receipt& value, std::int64_t point,
    bool& exact) noexcept {
  std::int64_t result = value.coefficients[0];
  for (std::uint8_t slot = 1; slot <= value.degree; ++slot) {
    std::int64_t product = 0; std::int64_t next = 0;
    exact = exact && blind_integer_detail::multiply(result, point, product) &&
        blind_integer_detail::add(product, value.coefficients[slot], next);
    result = next;
  }
  return result;
}

}  // namespace holonics::organ::causal_linear_detail
