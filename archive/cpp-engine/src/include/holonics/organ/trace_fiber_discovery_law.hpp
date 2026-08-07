#pragma once

#include <holonics/organ/trace_fiber_feature_law.hpp>

namespace holonics::organ::trace_fiber_discovery_detail {
namespace rational = exact::small_rational_law;

HOLONICS_CALLABLE inline void candidate(
    const trace_fiber_basis &basis, std::uint16_t rows,
    trace_fiber_target target, trace_fiber_feature_mode mode,
    trace_fiber_candidate_receipt &out) noexcept {
  out = {};
  out.rows = rows;
  out.target = target;
  out.mode = mode;
  out.features = trace_fiber_feature_detail::feature_count(mode);
  out.rank = basis.rank;
  out.nullity = static_cast<std::uint8_t>(out.features - out.rank);
  if (!basis.exact) {
    out.obstruction = trace_fiber_obstruction::invalid_exact_row;
    return;
  }
  if (rows < static_cast<std::uint16_t>(out.features - 1U)) {
    out.obstruction = trace_fiber_obstruction::insufficient_rows;
    return;
  }
  if (out.nullity == 0) {
    out.obstruction = trace_fiber_obstruction::full_rank;
    return;
  }
  if (out.nullity != 1) {
    out.obstruction = trace_fiber_obstruction::nonunique_kernel;
    return;
  }
  bool pivot[trace_fiber_feature_count]{};
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    pivot[basis.pivots[r]] = true;
  std::uint8_t free = 0;
  while (free < out.features && pivot[free])
    ++free;
  exact::small_rational vector[trace_fiber_feature_count]{};
  for (auto &value : vector)
    value = rational::make(0);
  vector[free] = rational::make(1);
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    vector[basis.pivots[r]] = rational::negate(basis.rows[r][free]);
  std::int64_t common = 1;
  for (std::uint8_t i = 0; i < out.features; ++i)
    common = rational::quotient(
        common * vector[i].denominator,
        rational::gcd(common, vector[i].denominator));
  std::int64_t divisor = 0;
  std::uint8_t reduced = 0;
  for (std::uint8_t column = 0; column < trace_fiber_feature_count; ++column)
    if (trace_fiber_feature_detail::admitted(column, mode)) {
      out.coefficients[column] = vector[reduced].numerator *
          rational::quotient(common, vector[reduced].denominator);
      divisor = rational::gcd(divisor, out.coefficients[column]);
      ++reduced;
    }
  for (auto &value : out.coefficients)
    value = rational::quotient(value, divisor);
  std::uint8_t first = 0;
  while (first < trace_fiber_feature_count && out.coefficients[first] == 0)
    ++first;
  if (first == trace_fiber_feature_count)
    return;
  if (out.coefficients[first] < 0)
    for (auto &value : out.coefficients)
      value = -value;
  out.primitive = true;
  out.obstruction = trace_fiber_obstruction::none;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
residual(const std::int64_t *coefficients,
         const transition_triple_receipt &triple,
         trace_fiber_target target) noexcept {
  std::int64_t values[trace_fiber_monomial_count]{};
  trace_fiber_feature_detail::monomials(triple.lower, values);
  std::int64_t sum = 0;
  for (std::uint8_t i = 0; i < trace_fiber_monomial_count; ++i)
    sum += coefficients[i] * values[i];
  return sum + coefficients[trace_fiber_monomial_count] *
                   triple.symmetric[static_cast<std::uint8_t>(target)];
}
[[nodiscard]] HOLONICS_CALLABLE inline bool same_coefficients(
    const trace_fiber_candidate_receipt &a,
    const trace_fiber_candidate_receipt &b) noexcept {
  for (std::uint8_t i = 0; i < trace_fiber_feature_count; ++i)
    if (a.coefficients[i] != b.coefficients[i])
      return false;
  return true;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool predict(
    const trace_fiber_organ &organ, const std::int64_t *lower,
    std::int64_t &target) noexcept {
  if (!organ.primitive || !organ.checker_founded)
    return false;
  std::int64_t values[trace_fiber_monomial_count]{};
  trace_fiber_feature_detail::monomials(lower, values);
  std::int64_t sum = 0;
  for (std::uint8_t i = 0; i < trace_fiber_monomial_count; ++i)
    sum += organ.coefficients[i] * values[i];
  const auto divisor = organ.coefficients[trace_fiber_monomial_count];
  if (divisor == 0 || rational::remainder(-sum, divisor) != 0)
    return false;
  target = rational::quotient(-sum, divisor);
  return true;
}

} // namespace holonics::organ::trace_fiber_discovery_detail
