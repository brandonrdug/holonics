#pragma once

#include <holonics/organ/characteristic_hypergeometry_receipt.hpp>

namespace holonics::organ::trace_law_detail {
namespace rational = exact::small_rational_law;

HOLONICS_CALLABLE inline void
features(const characteristic_pair_receipt &p,
         std::int64_t (&v)[characteristic_feature_count]) noexcept {
  const auto x = p.trace_first, y = p.trace_second, z = p.trace_product,
             k = p.trace_closed;
  const std::int64_t formed[characteristic_feature_count]{
      1,         x,         y,         z,         x * x,     x * y,
      x * z,     y * y,     y * z,     z * z,     x * x * x, x * x * y,
      x * x * z, x * y * y, x * y * z, x * z * z, y * y * y, y * y * z,
      y * z * z, z * z * z, k};
  for (std::uint8_t i = 0; i < characteristic_feature_count; ++i)
    v[i] = formed[i];
}

[[nodiscard]] HOLONICS_CALLABLE inline bool
admitted_column(std::uint8_t column, std::uint8_t mode) noexcept {
  if (mode == 1)
    return column <= 9 || column == 20;
  if (mode == 2)
    return column != 14;
  return true;
}

HOLONICS_CALLABLE inline bool insert(trace_basis &basis,
                                     const characteristic_pair_receipt &pair,
                                     std::uint8_t mode) noexcept {
  std::int64_t raw[characteristic_feature_count]{};
  features(pair, raw);
  exact::small_rational row[characteristic_feature_count]{};
  std::uint8_t count = 0;
  for (std::uint8_t i = 0; i < characteristic_feature_count; ++i)
    if (admitted_column(i, mode))
      row[count++] = rational::make(raw[i]);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto pivot = basis.pivots[r];
    const auto factor = row[pivot];
    if (factor.numerator == 0)
      continue;
    for (std::uint8_t c = pivot; c < count; ++c)
      row[c] = rational::subtract(row[c],
                                  rational::multiply(factor, basis.rows[r][c]));
  }
  std::uint8_t pivot = 0;
  while (pivot < count && row[pivot].numerator == 0)
    ++pivot;
  if (pivot == count)
    return false;
  const auto divisor = row[pivot];
  for (std::uint8_t c = pivot; c < count; ++c)
    row[c] = rational::divide(row[c], divisor);
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto factor = basis.rows[r][pivot];
    if (factor.numerator == 0)
      continue;
    for (std::uint8_t c = pivot; c < count; ++c)
      basis.rows[r][c] = rational::subtract(basis.rows[r][c],
                                            rational::multiply(factor, row[c]));
  }
  std::uint8_t at = 0;
  while (at < basis.rank && basis.pivots[at] < pivot)
    ++at;
  for (std::uint8_t r = basis.rank; r > at; --r) {
    basis.pivots[r] = basis.pivots[r - 1];
    for (std::uint8_t c = 0; c < count; ++c)
      basis.rows[r][c] = basis.rows[r - 1][c];
  }
  basis.pivots[at] = pivot;
  for (std::uint8_t c = 0; c < count; ++c)
    basis.rows[at][c] = row[c];
  ++basis.rank;
  return true;
}

HOLONICS_CALLABLE inline void
candidate(const trace_basis &basis, std::uint16_t rows, std::uint8_t mode,
          trace_law_candidate_receipt &out) noexcept {
  out = {};
  out.rows = rows;
  out.features =
      mode == 1 ? 11 : (mode == 2 ? 20 : characteristic_feature_count);
  out.rank = basis.rank;
  out.nullity = static_cast<std::uint8_t>(out.features - out.rank);
  if (rows < out.features - 1U) {
    out.obstruction = hypergeometry_trace_obstruction::insufficient_rows;
    return;
  }
  if (out.nullity == 0) {
    out.obstruction = hypergeometry_trace_obstruction::full_rank;
    return;
  }
  if (out.nullity != 1) {
    out.obstruction = hypergeometry_trace_obstruction::nonunique_kernel;
    return;
  }
  bool pivot[characteristic_feature_count]{};
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    pivot[basis.pivots[r]] = true;
  std::uint8_t free = 0;
  while (free < out.features && pivot[free])
    ++free;
  exact::small_rational vector[characteristic_feature_count]{};
  for (auto &value : vector)
    value = rational::make(0);
  vector[free] = rational::make(1);
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    vector[basis.pivots[r]] = rational::negate(basis.rows[r][free]);
  std::int64_t common = 1;
  for (std::uint8_t i = 0; i < out.features; ++i)
    common = rational::quotient(common * vector[i].denominator,
                                rational::gcd(common, vector[i].denominator));
  std::int64_t divisor = 0;
  std::uint8_t reduced = 0;
  for (std::uint8_t column = 0; column < characteristic_feature_count; ++column)
    if (admitted_column(column, mode)) {
      out.coefficients[column] =
          vector[reduced].numerator *
          rational::quotient(common, vector[reduced].denominator);
      divisor = rational::gcd(divisor, out.coefficients[column]);
      ++reduced;
    }
  for (auto &value : out.coefficients)
    value = rational::quotient(value, divisor);
  std::uint8_t first = 0;
  while (first < characteristic_feature_count && out.coefficients[first] == 0)
    ++first;
  if (first == characteristic_feature_count)
    return;
  if (out.coefficients[first] < 0)
    for (auto &value : out.coefficients)
      value = -value;
  out.primitive = true;
  out.obstruction = hypergeometry_trace_obstruction::none;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
residual(const std::int64_t *coefficients,
         const characteristic_pair_receipt &pair) noexcept {
  std::int64_t value[characteristic_feature_count]{};
  features(pair, value);
  std::int64_t sum = 0;
  for (std::uint8_t i = 0; i < characteristic_feature_count; ++i)
    sum += coefficients[i] * value[i];
  return sum;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
predict(const trace_law_organ &organ, std::int64_t x, std::int64_t y,
        std::int64_t z) noexcept {
  characteristic_pair_receipt face{};
  face.trace_first = x;
  face.trace_second = y;
  face.trace_product = z;
  std::int64_t value[characteristic_feature_count]{};
  features(face, value);
  std::int64_t sum = 0;
  for (std::uint8_t i = 0; i + 1U < characteristic_feature_count; ++i)
    sum += organ.coefficients[i] * value[i];
  const auto divisor = organ.coefficients[20];
  return -rational::quotient(sum, divisor);
}

} // namespace holonics::organ::trace_law_detail
