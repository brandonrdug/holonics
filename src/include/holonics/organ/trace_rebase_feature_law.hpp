#pragma once

#include <holonics/organ/trace_rebase_matrix_law.hpp>

namespace holonics::organ::trace_rebase_feature_detail {
[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
residue(std::int64_t value) noexcept {
  value %= trace_rebase_rank_modulus;
  return value < 0 ? value + trace_rebase_rank_modulus : value;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
field_product(std::int64_t left, std::int64_t right) noexcept {
  return (left * right) % trace_rebase_rank_modulus;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
field_inverse(std::int64_t value) noexcept {
  std::int64_t out = 1;
  std::uint64_t exponent =
      static_cast<std::uint64_t>(trace_rebase_rank_modulus - 2);
  while (exponent != 0) {
    if ((exponent & 1U) != 0)
      out = field_product(out, value);
    value = field_product(value, value);
    exponent >>= 1U;
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
power(std::int64_t value, std::uint8_t exponent) noexcept {
  std::int64_t out = 1;
  for (std::uint8_t i = 0; i < exponent; ++i)
    out *= value;
  return out;
}
HOLONICS_CALLABLE inline void exponents(
    std::uint8_t index,
    std::uint8_t (&out)[trace_rebase_coordinate_count]) noexcept {
  std::uint8_t at = 0;
  for (std::uint8_t total = 0; total <= 3; ++total)
    for (std::uint8_t a = 0; a <= total; ++a)
      for (std::uint8_t b = 0; b <= total - a; ++b)
        for (std::uint8_t c = 0; c <= total - a - b; ++c)
          for (std::uint8_t d = 0; d <= total - a - b - c; ++d)
            for (std::uint8_t e = 0; e <= total - a - b - c - d; ++e)
              for (std::uint8_t f = 0; f <= total - a - b - c - d - e;
                   ++f) {
                const auto t = static_cast<std::uint8_t>(
                    total - a - b - c - d - e - f);
                if (at++ == index) {
                  const std::uint8_t values[trace_rebase_coordinate_count]{
                      a, b, c, d, e, f, t};
                  for (std::uint8_t i = 0; i < trace_rebase_coordinate_count;
                       ++i)
                    out[i] = values[i];
                  return;
                }
              }
}
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t
monomial_count(std::uint8_t degree) noexcept {
  return degree == 0 ? 1U : (degree == 1 ? 8U : (degree == 2 ? 36U : 120U));
}
HOLONICS_CALLABLE inline void monomials(
    const std::int64_t *coordinates,
    std::int64_t (&out)[trace_rebase_monomial_count]) noexcept {
  for (std::uint8_t i = 0; i < trace_rebase_monomial_count; ++i) {
    std::uint8_t powers[trace_rebase_coordinate_count]{};
    exponents(i, powers);
    out[i] = 1;
    for (std::uint8_t j = 0; j < trace_rebase_coordinate_count; ++j)
      out[i] *= power(coordinates[j], powers[j]);
  }
}
HOLONICS_CALLABLE inline void reset(trace_rebase_basis &basis) noexcept {
  for (std::uint8_t i = 0; i < trace_rebase_feature_count; ++i) {
    basis.pivots[i] = 0;
    for (std::uint8_t j = 0; j < trace_rebase_joint_column_count; ++j)
      basis.rows[i][j] = 0;
  }
  basis.rank = 0;
  basis.exact = true;
}
HOLONICS_CALLABLE inline bool insert_values(
    trace_rebase_basis &basis, const std::int64_t *values,
    std::uint8_t columns) noexcept {
  std::int64_t row[trace_rebase_feature_count]{};
  for (std::uint8_t i = 0; i < columns; ++i)
    row[i] = residue(values[i]);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto pivot = basis.pivots[r];
    const auto factor = row[pivot];
    if (factor == 0)
      continue;
    for (std::uint8_t c = pivot; c < columns; ++c)
      row[c] = residue(
          row[c] - field_product(factor, basis.rows[r][c]));
  }
  std::uint8_t pivot = 0;
  while (pivot < columns && row[pivot] == 0)
    ++pivot;
  if (pivot == columns)
    return false;
  const auto divisor = field_inverse(row[pivot]);
  for (std::uint8_t c = pivot; c < columns; ++c)
    row[c] = field_product(row[c], divisor);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto factor = basis.rows[r][pivot];
    if (factor == 0)
      continue;
    for (std::uint8_t c = pivot; c < columns; ++c)
      basis.rows[r][c] = residue(
          basis.rows[r][c] - field_product(factor, row[c]));
  }
  std::uint8_t at = 0;
  while (at < basis.rank && basis.pivots[at] < pivot)
    ++at;
  for (std::uint8_t r = basis.rank; r > at; --r) {
    basis.pivots[r] = basis.pivots[r - 1U];
    for (std::uint8_t c = 0; c < columns; ++c)
      basis.rows[r][c] = basis.rows[r - 1U][c];
  }
  basis.pivots[at] = pivot;
  for (std::uint8_t c = 0; c < columns; ++c)
    basis.rows[at][c] = row[c];
  ++basis.rank;
  return true;
}
HOLONICS_CALLABLE inline bool insert_joint(
    trace_rebase_basis &basis, const std::int64_t *values,
    std::uint8_t feature_columns, std::uint8_t total_columns) noexcept {
  std::int64_t row[trace_rebase_joint_column_count]{};
  for (std::uint8_t i = 0; i < total_columns; ++i)
    row[i] = residue(values[i]);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto pivot = basis.pivots[r];
    const auto factor = row[pivot];
    if (factor == 0)
      continue;
    for (std::uint8_t c = pivot; c < total_columns; ++c)
      row[c] = residue(
          row[c] - field_product(factor, basis.rows[r][c]));
  }
  std::uint8_t pivot = 0;
  while (pivot < feature_columns && row[pivot] == 0)
    ++pivot;
  if (pivot == feature_columns)
    return false;
  const auto divisor = field_inverse(row[pivot]);
  for (std::uint8_t c = pivot; c < total_columns; ++c)
    row[c] = field_product(row[c], divisor);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto factor = basis.rows[r][pivot];
    if (factor == 0)
      continue;
    for (std::uint8_t c = pivot; c < total_columns; ++c)
      basis.rows[r][c] = residue(
          basis.rows[r][c] - field_product(factor, row[c]));
  }
  std::uint8_t at = 0;
  while (at < basis.rank && basis.pivots[at] < pivot)
    ++at;
  for (std::uint8_t r = basis.rank; r > at; --r) {
    basis.pivots[r] = basis.pivots[r - 1U];
    for (std::uint8_t c = 0; c < total_columns; ++c)
      basis.rows[r][c] = basis.rows[r - 1U][c];
  }
  basis.pivots[at] = pivot;
  for (std::uint8_t c = 0; c < total_columns; ++c)
    basis.rows[at][c] = row[c];
  ++basis.rank;
  return true;
}
HOLONICS_CALLABLE inline bool insert(
    trace_rebase_basis &basis, const std::int64_t *source,
    std::int64_t target, std::uint8_t degree) noexcept {
  std::int64_t values[trace_rebase_feature_count]{};
  std::int64_t source_values[trace_rebase_monomial_count]{};
  monomials(source, source_values);
  const auto monomials_used = monomial_count(degree);
  for (std::uint8_t i = 0; i < monomials_used; ++i)
    values[i] = source_values[i];
  values[monomials_used] = target;
  return insert_values(
      basis, values, static_cast<std::uint8_t>(monomials_used + 1U));
}

} // namespace holonics::organ::trace_rebase_feature_detail
