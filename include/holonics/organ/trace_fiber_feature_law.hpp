#pragma once

#include <holonics/organ/trace_fiber_receipt.hpp>

namespace holonics::organ::trace_fiber_feature_detail {
namespace rational = exact::small_rational_law;

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
power(std::int64_t value, std::uint8_t exponent) noexcept {
  std::int64_t out = 1;
  for (std::uint8_t i = 0; i < exponent; ++i)
    out *= value;
  return out;
}
HOLONICS_CALLABLE inline void exponents(std::uint8_t index,
                                        std::uint8_t (&out)[6]) noexcept {
  std::uint8_t at = 0;
  for (std::uint8_t total = 0; total <= 3; ++total)
    for (std::uint8_t a = 0; a <= total; ++a)
      for (std::uint8_t b = 0; b <= total - a; ++b)
        for (std::uint8_t c = 0; c <= total - a - b; ++c)
          for (std::uint8_t d = 0; d <= total - a - b - c; ++d)
            for (std::uint8_t e = 0; e <= total - a - b - c - d; ++e) {
              const std::uint8_t f =
                  static_cast<std::uint8_t>(total - a - b - c - d - e);
              if (at++ == index) {
                const std::uint8_t values[6]{a, b, c, d, e, f};
                for (std::uint8_t i = 0; i < 6; ++i)
                  out[i] = values[i];
                return;
              }
            }
}
HOLONICS_CALLABLE inline void
monomials(const std::int64_t *lower,
          std::int64_t (&out)[trace_fiber_monomial_count]) noexcept {
  for (std::uint8_t i = 0; i < trace_fiber_monomial_count; ++i) {
    std::uint8_t powers[6]{};
    exponents(i, powers);
    out[i] = 1;
    for (std::uint8_t j = 0; j < 6; ++j)
      out[i] *= power(lower[j], powers[j]);
  }
}
[[nodiscard]] HOLONICS_CALLABLE inline bool
admitted(std::uint8_t column, trace_fiber_feature_mode mode) noexcept {
  if (column == trace_fiber_monomial_count)
    return mode != trace_fiber_feature_mode::target_deleted;
  std::uint8_t powers[6]{};
  exponents(column, powers);
  const auto degree = static_cast<std::uint8_t>(
      powers[0] + powers[1] + powers[2] + powers[3] + powers[4] + powers[5]);
  if (mode == trace_fiber_feature_mode::degree_two)
    return degree <= 2;
  if (mode == trace_fiber_feature_mode::sixth_coordinate_deleted)
    return powers[5] == 0;
  return true;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::uint8_t
feature_count(trace_fiber_feature_mode mode) noexcept {
  std::uint8_t count = 0;
  for (std::uint8_t i = 0; i < trace_fiber_feature_count; ++i)
    count = static_cast<std::uint8_t>(count + (admitted(i, mode) ? 1U : 0U));
  return count;
}
HOLONICS_CALLABLE inline bool insert(trace_fiber_basis &basis,
                                     const transition_triple_receipt &triple,
                                     trace_fiber_target target,
                                     trace_fiber_feature_mode mode) noexcept {
  std::int64_t values[trace_fiber_monomial_count]{};
  monomials(triple.lower, values);
  exact::small_rational row[trace_fiber_feature_count]{};
  std::uint8_t count = 0;
  for (std::uint8_t i = 0; i < trace_fiber_feature_count; ++i)
    if (admitted(i, mode)) {
      const auto value = i == trace_fiber_monomial_count
                             ? triple.symmetric[static_cast<std::uint8_t>(target)]
                             : values[i];
      row[count++] = rational::make(value);
    }
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto pivot = basis.pivots[r];
    const auto factor = row[pivot];
    if (factor.numerator == 0)
      continue;
    for (std::uint8_t c = pivot; c < count; ++c) {
      row[c] = rational::subtract(
          row[c], rational::multiply(factor, basis.rows[r][c]));
      basis.exact = basis.exact && rational::valid(row[c]);
    }
  }
  std::uint8_t pivot = 0;
  while (pivot < count && row[pivot].numerator == 0)
    ++pivot;
  if (pivot == count)
    return false;
  const auto divisor = row[pivot];
  for (std::uint8_t c = pivot; c < count; ++c) {
    row[c] = rational::divide(row[c], divisor);
    basis.exact = basis.exact && rational::valid(row[c]);
  }
  for (std::uint8_t r = 0; r < basis.rank; ++r) {
    const auto factor = basis.rows[r][pivot];
    if (factor.numerator == 0)
      continue;
    for (std::uint8_t c = pivot; c < count; ++c)
      basis.rows[r][c] = rational::subtract(
          basis.rows[r][c], rational::multiply(factor, row[c]));
  }
  std::uint8_t at = 0;
  while (at < basis.rank && basis.pivots[at] < pivot)
    ++at;
  for (std::uint8_t r = basis.rank; r > at; --r) {
    basis.pivots[r] = basis.pivots[r - 1U];
    for (std::uint8_t c = 0; c < count; ++c)
      basis.rows[r][c] = basis.rows[r - 1U][c];
  }
  basis.pivots[at] = pivot;
  for (std::uint8_t c = 0; c < count; ++c)
    basis.rows[at][c] = row[c];
  ++basis.rank;
  return true;
}

} // namespace holonics::organ::trace_fiber_feature_detail
