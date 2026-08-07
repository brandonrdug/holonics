#pragma once

#include <holonics/organ/blind_integer_exact.hpp>

namespace holonics::organ::blind_polynomial_detail {

inline constexpr std::size_t polynomial_work_capacity = 9;

struct polynomial final {
  std::int64_t coefficients[polynomial_work_capacity]{};
  std::uint8_t degree{};
  bool exact{true};
};

HOLONICS_CALLABLE constexpr void normalize(polynomial& value) noexcept {
  while (value.degree > 0 && value.coefficients[value.degree] == 0) { --value.degree; }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool zero(const polynomial& value) noexcept {
  return value.degree == 0 && value.coefficients[0] == 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr polynomial constant(std::int64_t value) noexcept {
  polynomial out{};
  out.coefficients[0] = value;
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr polynomial linear(
    std::int64_t constant_value, std::int64_t x_value) noexcept {
  polynomial out{};
  out.coefficients[0] = constant_value;
  out.coefficients[1] = x_value;
  out.degree = x_value == 0 ? 0U : 1U;
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr polynomial subtract(
    const polynomial& left, const polynomial& right) noexcept {
  polynomial out{};
  out.degree = left.degree > right.degree ? left.degree : right.degree;
  out.exact = left.exact && right.exact;
  for (std::uint8_t slot = 0; slot <= out.degree; ++slot) {
    out.exact = out.exact && blind_integer_detail::subtract(
        left.coefficients[slot], right.coefficients[slot], out.coefficients[slot]);
  }
  normalize(out);
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr polynomial multiply(
    const polynomial& left, const polynomial& right) noexcept {
  polynomial out{};
  if (left.degree + right.degree >= polynomial_work_capacity) {
    out.exact = false; return out;
  }
  out.degree = static_cast<std::uint8_t>(left.degree + right.degree);
  out.exact = left.exact && right.exact;
  for (std::uint8_t i = 0; i <= left.degree; ++i) {
    for (std::uint8_t j = 0; j <= right.degree; ++j) {
      std::int64_t product = 0;
      std::int64_t sum = 0;
      out.exact = out.exact && blind_integer_detail::multiply(
          left.coefficients[i], right.coefficients[j], product) &&
          blind_integer_detail::add(out.coefficients[i + j], product, sum);
      out.coefficients[i + j] = sum;
    }
  }
  normalize(out);
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr polynomial divide_exact(
    const polynomial& numerator, const polynomial& denominator) noexcept {
  polynomial quotient{};
  quotient.exact = numerator.exact && denominator.exact && !zero(denominator);
  if (!quotient.exact || numerator.degree < denominator.degree) {
    quotient.exact = quotient.exact && zero(numerator); return quotient;
  }
  polynomial remainder = numerator;
  quotient.degree = static_cast<std::uint8_t>(numerator.degree - denominator.degree);
  while (!zero(remainder) && remainder.degree >= denominator.degree) {
    const auto shift = static_cast<std::uint8_t>(remainder.degree - denominator.degree);
    const auto leading = denominator.coefficients[denominator.degree];
    std::int64_t factor = 0;
    if (!blind_integer_detail::divide_exact(
            remainder.coefficients[remainder.degree], leading, factor)) {
      quotient.exact = false; return quotient;
    }
    quotient.coefficients[shift] = factor;
    for (std::uint8_t slot = 0; slot <= denominator.degree; ++slot) {
      std::int64_t product = 0;
      std::int64_t difference = 0;
      quotient.exact = quotient.exact && blind_integer_detail::multiply(
          factor, denominator.coefficients[slot], product) &&
          blind_integer_detail::subtract(
              remainder.coefficients[slot + shift], product, difference);
      remainder.coefficients[slot + shift] = difference;
    }
    normalize(remainder);
  }
  quotient.exact = quotient.exact && zero(remainder);
  normalize(quotient);
  return quotient;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr polynomial determinant_pencil(
    const std::int64_t (&hankel)[blind_moment_degree_capacity][blind_moment_degree_capacity],
    const std::int64_t (&shifted)[blind_moment_degree_capacity][blind_moment_degree_capacity],
    std::uint8_t size) noexcept {
  polynomial matrix[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  for (std::uint8_t row = 0; row < size; ++row) {
    for (std::uint8_t column = 0; column < size; ++column) {
      matrix[row][column] = linear(-shifted[row][column], hankel[row][column]);
    }
  }
  polynomial previous = constant(1);
  bool negative = false;
  for (std::uint8_t pivot = 0; pivot + 1U < size; ++pivot) {
    if (zero(matrix[pivot][pivot])) {
      std::uint8_t replacement = static_cast<std::uint8_t>(pivot + 1U);
      while (replacement < size && zero(matrix[replacement][pivot])) { ++replacement; }
      if (replacement == size) { return constant(0); }
      for (std::uint8_t column = 0; column < size; ++column) {
        const auto held = matrix[pivot][column];
        matrix[pivot][column] = matrix[replacement][column];
        matrix[replacement][column] = held;
      }
      negative = !negative;
    }
    const auto diagonal = matrix[pivot][pivot];
    for (std::uint8_t row = static_cast<std::uint8_t>(pivot + 1U); row < size; ++row) {
      for (std::uint8_t column = static_cast<std::uint8_t>(pivot + 1U);
          column < size; ++column) {
        const auto numerator = subtract(multiply(matrix[row][column], diagonal),
            multiply(matrix[row][pivot], matrix[pivot][column]));
        matrix[row][column] = divide_exact(numerator, previous);
        if (!matrix[row][column].exact) { return matrix[row][column]; }
      }
    }
    previous = diagonal;
  }
  auto result = matrix[size - 1U][size - 1U];
  if (negative) {
    for (std::uint8_t slot = 0; slot <= result.degree; ++slot) {
      result.coefficients[slot] = -result.coefficients[slot];
    }
  }
  return result;
}

}  // namespace holonics::organ::blind_polynomial_detail
