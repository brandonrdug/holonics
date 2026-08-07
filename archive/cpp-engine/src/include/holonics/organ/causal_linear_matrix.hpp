#pragma once

#include <holonics/organ/causal_linear_receipt.hpp>
#include <holonics/organ/causal_linear_rational.hpp>

namespace holonics::organ::causal_linear_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_shape(
    const causal_integer_matrix& value) noexcept {
  return value.rows != 0 && value.rows <= causal_matrix_rows && value.columns != 0 &&
      value.columns <= causal_matrix_columns;
}

HOLONICS_CALLABLE constexpr void set_matrix(causal_integer_matrix& out,
    std::uint8_t rows, std::uint8_t columns, std::uint64_t identity,
    std::uint64_t lineage) noexcept {
  out.rows = rows; out.columns = columns; out.identity = exact::word{identity};
  out.lineage = exact::word{lineage}; out.exact = rows != 0 && rows <= causal_matrix_rows &&
      columns != 0 && columns <= causal_matrix_columns;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(
    const causal_integer_matrix& left, const causal_integer_matrix& right,
    causal_integer_matrix& out, std::uint64_t identity) noexcept {
  if (!valid_shape(left) || !valid_shape(right) || left.columns != right.rows ||
      right.columns > causal_matrix_columns) { return false; }
  set_matrix(out, left.rows, right.columns, identity,
      left.lineage.value() + right.lineage.value());
  bool exact = out.exact;
  for (std::uint8_t row = 0; row < out.rows; ++row) {
    for (std::uint8_t column = 0; column < out.columns; ++column) {
      std::int64_t sum = 0;
      for (std::uint8_t inner = 0; inner < left.columns; ++inner) {
        std::int64_t product = 0; std::int64_t next = 0;
        exact = exact && blind_integer_detail::multiply(
            left.values[row][inner], right.values[inner][column], product) &&
            blind_integer_detail::add(sum, product, next);
        sum = next;
      }
      out.values[row][column] = sum;
    }
  }
  out.exact = exact; return exact;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool zero(
    const causal_integer_matrix& value) noexcept {
  if (!valid_shape(value) || !value.exact) { return false; }
  for (std::uint8_t row = 0; row < value.rows; ++row) {
    for (std::uint8_t column = 0; column < value.columns; ++column) {
      if (value.values[row][column] != 0) { return false; }
    }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void analyze(const causal_integer_matrix& source,
    causal_matrix_analysis& out, std::uint64_t identity) noexcept {
  out.identity = exact::word{identity};
  out.lineage = exact::word{source.lineage.value() + 1U};
  if (!valid_shape(source) || !source.exact) { return; }
  exact::small_rational work[causal_matrix_rows][causal_matrix_columns]{}; bool exact = true;
  for (std::uint8_t row = 0; row < source.rows; ++row) {
    for (std::uint8_t column = 0; column < source.columns; ++column) {
      exact = rational_make(source.values[row][column], work[row][column]) && exact;
    }
  }
  if (!exact) { return; }
  std::uint8_t pivot_row = 0;
  for (std::uint8_t column = 0; column < source.columns && pivot_row < source.rows; ++column) {
    std::uint8_t found = pivot_row;
    while (found < source.rows && work[found][column].numerator == 0) { ++found; }
    if (found == source.rows) { continue; }
    for (std::uint8_t slot = 0; slot < source.columns; ++slot) {
      const auto temporary = work[pivot_row][slot];
      work[pivot_row][slot] = work[found][slot]; work[found][slot] = temporary;
    }
    const auto pivot = work[pivot_row][column];
    for (std::uint8_t slot = 0; slot < source.columns; ++slot) {
      exact::small_rational quotient{};
      if (!rational_divide(work[pivot_row][slot], pivot, quotient)) { return; }
      work[pivot_row][slot] = quotient;
    }
    for (std::uint8_t row = 0; row < source.rows; ++row) {
      if (row == pivot_row || work[row][column].numerator == 0) { continue; }
      const auto scale = work[row][column];
      for (std::uint8_t slot = 0; slot < source.columns; ++slot) {
        exact::small_rational product{}; exact::small_rational difference{};
        if (!rational_multiply(scale, work[pivot_row][slot], product) ||
            !rational_subtract(work[row][slot], product, difference)) { return; }
        work[row][slot] = difference;
      }
    }
    out.pivot_columns[pivot_row] = column; ++pivot_row;
  }
  out.rank = pivot_row; out.nullity = static_cast<std::uint8_t>(source.columns - pivot_row);
  for (std::uint8_t column = 0; column < source.columns; ++column) {
    bool pivot = false;
    for (std::uint8_t row = 0; row < pivot_row; ++row) {
      pivot = pivot || out.pivot_columns[row] == column;
    }
    if (pivot) { continue; }
    if (out.kernel_count >= causal_kernel_capacity) { return; }
    auto& vector = out.kernel[out.kernel_count];
    for (std::uint8_t slot = 0; slot < source.columns; ++slot) {
      vector[slot] = {0, 1};
    }
    vector[column] = {1, 1};
    for (std::uint8_t row = 0; row < pivot_row; ++row) {
      if (!rational_negate(work[row][column], vector[out.pivot_columns[row]])) { return; }
    }
    ++out.kernel_count;
  }
  bool valid = out.kernel_count == out.nullity;
  for (std::uint8_t basis = 0; basis < out.kernel_count; ++basis) {
    for (std::uint8_t row = 0; row < source.rows; ++row) {
      exact::small_rational sum{0, 1};
      for (std::uint8_t column = 0; column < source.columns; ++column) {
        exact::small_rational coefficient{}; exact::small_rational product{};
        exact::small_rational next{};
        valid = rational_make(source.values[row][column], coefficient) &&
            rational_multiply(coefficient, out.kernel[basis][column], product) &&
            rational_add(sum, product, next) && valid;
        sum = next;
      }
      valid = valid && sum.numerator == 0 && rational_valid(sum);
    }
  }
  out.exact = valid;
}

HOLONICS_CALLABLE constexpr bool smith_rank_two(const causal_integer_matrix& source,
    const causal_matrix_analysis& analysis, std::int64_t (&out)[2]) noexcept {
  if (!analysis.exact || analysis.rank == 0 || analysis.rank > 2) { return false; }
  std::int64_t first = 0;
  for (std::uint8_t row = 0; row < source.rows; ++row) {
    for (std::uint8_t column = 0; column < source.columns; ++column) {
      const auto value = source.values[row][column];
      if (value == 0) { continue; }
      std::int64_t magnitude = value;
      if (magnitude < 0 && !checked_negate(magnitude, magnitude)) { return false; }
      first = first == 0 ? magnitude : exact::small_rational_law::gcd(first, magnitude);
    }
  }
  out[0] = first;
  if (analysis.rank == 1) { return out[0] != 0; }
  std::int64_t second_divisor = 0;
  for (std::uint8_t r0 = 0; r0 < source.rows; ++r0) {
    for (std::uint8_t r1 = static_cast<std::uint8_t>(r0 + 1U); r1 < source.rows; ++r1) {
      for (std::uint8_t c0 = 0; c0 < source.columns; ++c0) {
        for (std::uint8_t c1 = static_cast<std::uint8_t>(c0 + 1U); c1 < source.columns; ++c1) {
          std::int64_t left = 0; std::int64_t right = 0; std::int64_t minor = 0;
          if (!blind_integer_detail::multiply(source.values[r0][c0],
                  source.values[r1][c1], left) ||
              !blind_integer_detail::multiply(source.values[r0][c1],
                  source.values[r1][c0], right) ||
              !blind_integer_detail::subtract(left, right, minor)) { return false; }
          if (minor != 0) {
            std::int64_t magnitude = minor;
            if (magnitude < 0 && !checked_negate(magnitude, magnitude)) { return false; }
            second_divisor = second_divisor == 0 ? magnitude :
                exact::small_rational_law::gcd(second_divisor, magnitude);
          }
        }
      }
    }
  }
  std::int64_t divisibility = 0;
  if (out[0] == 0 || !blind_integer_detail::divide_exact(
      second_divisor, out[0], out[1]) || out[1] == 0) { return false; }
  return blind_integer_detail::divide_exact(out[1], out[0], divisibility);
}

}  // namespace holonics::organ::causal_linear_detail
