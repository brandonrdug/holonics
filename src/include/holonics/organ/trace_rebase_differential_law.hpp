#pragma once

#include <holonics/organ/trace_fiber_discovery_law.hpp>
#include <holonics/organ/trace_rebase_discovery_law.hpp>

namespace holonics::organ::trace_rebase_differential_detail {
namespace rational = exact::small_rational_law;

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t derivative_monomial(
    const std::int64_t *coordinates, const std::uint8_t *powers,
    std::uint8_t variable, std::uint8_t variables) noexcept {
  if (powers[variable] == 0)
    return 0;
  std::int64_t out = powers[variable];
  for (std::uint8_t i = 0; i < variables; ++i) {
    auto exponent = powers[i];
    if (i == variable)
      --exponent;
    out *= trace_rebase_feature_detail::power(coordinates[i], exponent);
  }
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool organ_value_derivative(
    const trace_fiber_organ &organ, const std::int64_t *lower,
    std::int64_t &value, std::int64_t (&derivative)[6]) noexcept {
  if (!organ.primitive || !organ.checker_founded ||
      organ.identity.value() == 0 ||
      !trace_fiber_discovery_detail::predict(organ, lower, value))
    return false;
  const auto divisor = organ.coefficients[trace_fiber_monomial_count];
  for (std::uint8_t variable = 0; variable < 6; ++variable) {
    std::int64_t numerator = 0;
    for (std::uint8_t monomial = 0; monomial < trace_fiber_monomial_count;
         ++monomial) {
      std::uint8_t powers[6]{};
      trace_fiber_feature_detail::exponents(monomial, powers);
      numerator += organ.coefficients[monomial] * derivative_monomial(
          lower, powers, variable, 6);
    }
    if (rational::remainder(-numerator, divisor) != 0)
      return false;
    derivative[variable] = rational::quotient(-numerator, divisor);
  }
  return true;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool gradient(
    const trace_fiber_organ &sum, const trace_fiber_organ &product,
    const std::int64_t *coordinates,
    std::int64_t (&out)[trace_rebase_coordinate_count]) noexcept {
  std::int64_t s = 0, r = 0, ds[6]{}, dr[6]{};
  if (!organ_value_derivative(sum, coordinates, s, ds) ||
      !organ_value_derivative(product, coordinates, r, dr))
    return false;
  for (std::uint8_t i = 0; i < 6; ++i)
    out[i] = dr[i] - ds[i] * coordinates[6];
  out[6] = 2 * coordinates[6] - s;
  const auto f = coordinates[6] * coordinates[6] - s * coordinates[6] + r;
  return f == 0;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool map_jacobian(
    const trace_rebase_map_organ &map, const std::int64_t *source,
    std::int64_t (&out)[trace_rebase_coordinate_count]
                       [trace_rebase_coordinate_count]) noexcept {
  if (!map.primitive)
    return false;
  for (std::uint8_t target = 0; target < trace_rebase_coordinate_count;
       ++target) {
    const auto divisor = map.coefficients[target][trace_rebase_monomial_count];
    if (divisor == 0)
      return false;
    for (std::uint8_t variable = 0; variable < trace_rebase_coordinate_count;
         ++variable) {
      std::int64_t numerator = 0;
      for (std::uint8_t monomial = 0; monomial < trace_rebase_monomial_count;
           ++monomial) {
        std::uint8_t powers[trace_rebase_coordinate_count]{};
        trace_rebase_feature_detail::exponents(monomial, powers);
        numerator += map.coefficients[target][monomial] *
            derivative_monomial(source, powers, variable,
                                trace_rebase_coordinate_count);
      }
      if (rational::remainder(-numerator, divisor) != 0)
        return false;
      out[target][variable] = rational::quotient(-numerator, divisor);
    }
  }
  return true;
}
HOLONICS_CALLABLE inline std::uint8_t tangent(
    const std::int64_t *gradient,
    std::int64_t (&basis)[trace_rebase_tangent_rank]
                          [trace_rebase_coordinate_count]) noexcept {
  std::uint8_t pivot = 0;
  while (pivot < trace_rebase_coordinate_count && gradient[pivot] == 0)
    ++pivot;
  if (pivot == trace_rebase_coordinate_count)
    return 0;
  std::uint8_t at = 0;
  for (std::uint8_t free = 0; free < trace_rebase_coordinate_count; ++free) {
    if (free == pivot)
      continue;
    basis[at][free] = gradient[pivot];
    basis[at][pivot] = -gradient[free];
    ++at;
  }
  return at;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::uint8_t row_rank(
    const std::int64_t rows[trace_rebase_tangent_rank]
                           [trace_rebase_coordinate_count]) noexcept {
  exact::small_rational matrix[trace_rebase_tangent_rank]
                              [trace_rebase_coordinate_count]{};
  for (std::uint8_t i = 0; i < trace_rebase_tangent_rank; ++i)
    for (std::uint8_t j = 0; j < trace_rebase_coordinate_count; ++j)
      matrix[i][j] = rational::make(rows[i][j]);
  std::uint8_t rank = 0;
  for (std::uint8_t column = 0; column < trace_rebase_coordinate_count &&
                                rank < trace_rebase_tangent_rank;
       ++column) {
    std::uint8_t pivot = rank;
    while (pivot < trace_rebase_tangent_rank &&
           matrix[pivot][column].numerator == 0)
      ++pivot;
    if (pivot == trace_rebase_tangent_rank)
      continue;
    if (pivot != rank)
      for (std::uint8_t j = column; j < trace_rebase_coordinate_count; ++j) {
        const auto temporary = matrix[rank][j];
        matrix[rank][j] = matrix[pivot][j];
        matrix[pivot][j] = temporary;
      }
    const auto divisor = matrix[rank][column];
    for (std::uint8_t j = column; j < trace_rebase_coordinate_count; ++j)
      matrix[rank][j] = rational::divide(matrix[rank][j], divisor);
    for (std::uint8_t row = 0; row < trace_rebase_tangent_rank; ++row) {
      if (row == rank || matrix[row][column].numerator == 0)
        continue;
      const auto factor = matrix[row][column];
      for (std::uint8_t j = column; j < trace_rebase_coordinate_count; ++j)
        matrix[row][j] = rational::subtract(
            matrix[row][j], rational::multiply(factor, matrix[rank][j]));
    }
    ++rank;
  }
  return rank;
}
HOLONICS_CALLABLE inline void transport(
    const std::int64_t jacobian[trace_rebase_coordinate_count]
                               [trace_rebase_coordinate_count],
    const std::int64_t tangent[trace_rebase_tangent_rank]
                              [trace_rebase_coordinate_count],
    std::int64_t (&out)[trace_rebase_tangent_rank]
                       [trace_rebase_coordinate_count]) noexcept {
  for (std::uint8_t vector = 0; vector < trace_rebase_tangent_rank; ++vector)
    for (std::uint8_t row = 0; row < trace_rebase_coordinate_count; ++row)
      for (std::uint8_t column = 0; column < trace_rebase_coordinate_count;
           ++column)
        out[vector][row] += jacobian[row][column] * tangent[vector][column];
}
[[nodiscard]] HOLONICS_CALLABLE inline bool deck_vertical(
    const trace_fiber_organ (&fiber)[2], const trace_rebase_state &state,
    trace_rebase_witness &out) noexcept {
  std::int64_t sum = 0, derivative[6]{};
  std::int64_t constraint[trace_rebase_coordinate_count]{};
  if (!state.branch ||
      !organ_value_derivative(fiber[0], state.coordinates, sum,
                              derivative) ||
      !gradient(fiber[0], fiber[1], state.coordinates,
                constraint) ||
      constraint[6] != 0 || 2 * state.coordinates[6] != sum)
    return false;
  bool smooth = false;
  for (const auto value : constraint)
    smooth = smooth || value != 0;
  if (!smooth)
    return false;
  out = {};
  out.kind = 3;
  out.first = state.ordinal;
  out.vector[6] = 1;
  for (std::uint8_t i = 0; i < 6; ++i)
    out.image[i] = out.vector[i];
  out.image[6] = -out.vector[6];
  out.eigenvalue = rational::quotient(out.image[6], out.vector[6]);
  out.found = true;
  for (std::uint8_t i = 0; i < trace_rebase_coordinate_count; ++i)
    out.found = out.found && out.image[i] == out.eigenvalue * out.vector[i];
  return out.found;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool chain(
    const std::int64_t gradient[trace_rebase_coordinate_count],
    const std::int64_t transported[trace_rebase_tangent_rank]
                                  [trace_rebase_coordinate_count]) noexcept {
  for (std::uint8_t vector = 0; vector < trace_rebase_tangent_rank; ++vector) {
    std::int64_t residual = 0;
    for (std::uint8_t i = 0; i < trace_rebase_coordinate_count; ++i)
      residual += gradient[i] * transported[vector][i];
    if (residual != 0)
      return false;
  }
  return true;
}

} // namespace holonics::organ::trace_rebase_differential_detail
