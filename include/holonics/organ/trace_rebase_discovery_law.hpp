#pragma once

#include <holonics/organ/trace_rebase_feature_law.hpp>

namespace holonics::organ::trace_rebase_discovery_detail {
namespace rational = exact::small_rational_law;

HOLONICS_CALLABLE inline void candidate(
    const trace_rebase_basis &basis, trace_rebase_move move,
    std::uint8_t target, std::uint8_t degree, std::uint16_t rows,
    trace_rebase_candidate &out) noexcept {
  out = {};
  out.rows = rows;
  out.move = move;
  out.target = target;
  out.degree = degree;
  const auto monomials = trace_rebase_feature_detail::monomial_count(degree);
  out.features = static_cast<std::uint8_t>(monomials + 1U);
  out.rank = basis.rank;
  out.nullity = static_cast<std::uint8_t>(out.features - out.rank);
  if (!basis.exact) {
    out.obstruction = trace_rebase_obstruction::invalid_exact_row;
    return;
  }
  if (out.rank == out.features) {
    out.obstruction = trace_rebase_obstruction::full_rank;
    return;
  }
  if (out.nullity != 1) {
    out.obstruction = trace_rebase_obstruction::nonunique_kernel;
    return;
  }
  bool pivot[trace_rebase_feature_count]{};
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    pivot[basis.pivots[r]] = true;
  std::uint8_t free = 0;
  while (free < out.features && pivot[free])
    ++free;
  std::int64_t vector[trace_rebase_feature_count]{};
  vector[free] = 1;
  for (std::uint8_t r = 0; r < basis.rank; ++r)
    vector[basis.pivots[r]] = trace_rebase_feature_detail::residue(
        -basis.rows[r][free]);
  if (vector[monomials] == 0)
    return;
  const auto scale =
      trace_rebase_feature_detail::field_inverse(vector[monomials]);
  for (std::uint8_t i = 0; i < out.features; ++i) {
    auto value = trace_rebase_feature_detail::field_product(vector[i], scale);
    if (value > trace_rebase_rank_modulus / 2)
      value -= trace_rebase_rank_modulus;
    if (i == monomials)
      out.coefficients[trace_rebase_monomial_count] = value;
    else
      out.coefficients[i] = value;
  }
  out.primitive = true;
  out.obstruction = trace_rebase_obstruction::none;
}
[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t residual(
    const std::int64_t *coefficients, const std::int64_t *source,
    std::int64_t target) noexcept {
  std::int64_t values[trace_rebase_monomial_count]{};
  trace_rebase_feature_detail::monomials(source, values);
  std::int64_t sum = 0;
  for (std::uint8_t i = 0; i < trace_rebase_monomial_count; ++i)
    sum += coefficients[i] * values[i];
  return sum + coefficients[trace_rebase_monomial_count] * target;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool predict(
    const std::int64_t *coefficients, const std::int64_t *source,
    std::int64_t &target) noexcept {
  std::int64_t values[trace_rebase_monomial_count]{};
  trace_rebase_feature_detail::monomials(source, values);
  std::int64_t sum = 0;
  for (std::uint8_t i = 0; i < trace_rebase_monomial_count; ++i)
    sum += coefficients[i] * values[i];
  const auto divisor = coefficients[trace_rebase_monomial_count];
  if (divisor == 0 || rational::remainder(-sum, divisor) != 0)
    return false;
  target = rational::quotient(-sum, divisor);
  return true;
}
HOLONICS_CALLABLE inline bool discover_filtered(
    const trace_rebase_discovery_receipt &ecology, trace_rebase_move move,
    std::uint8_t target, trace_rebase_workspace &workspace,
    trace_rebase_candidate &out, std::uint8_t excluded_source,
    std::uint8_t maximum_degree = 3) noexcept {
  std::uint16_t admitted_rows = 0;
  for (std::uint16_t state = 0; state < ecology.state_count; ++state)
    admitted_rows = static_cast<std::uint16_t>(
        admitted_rows + (ecology.states[state].source != excluded_source));
  for (std::uint8_t degree = 0; degree <= maximum_degree; ++degree) {
    trace_rebase_feature_detail::reset(workspace.basis);
    const auto columns = static_cast<std::uint8_t>(
        trace_rebase_feature_detail::monomial_count(degree) + 1U);
    for (std::uint16_t state = 0; state < ecology.state_count &&
                                  workspace.basis.rank < columns;
         ++state) {
      if (ecology.states[state].source == excluded_source)
        continue;
      const auto edge = static_cast<std::uint16_t>(
          state * trace_rebase_move_count + static_cast<std::uint8_t>(move));
      trace_rebase_feature_detail::insert(
          workspace.basis, ecology.states[state].coordinates,
          ecology.edges[edge].target[target], degree);
    }
    candidate(workspace.basis, move, target, degree, admitted_rows, out);
    if (out.obstruction != trace_rebase_obstruction::none)
      continue;
    bool exact = true;
    for (std::uint16_t state = 0; state < ecology.state_count; ++state) {
      if (ecology.states[state].source == excluded_source)
        continue;
      const auto edge = static_cast<std::uint16_t>(
          state * trace_rebase_move_count + static_cast<std::uint8_t>(move));
      exact = exact && residual(out.coefficients,
                                ecology.states[state].coordinates,
                                ecology.edges[edge].target[target]) == 0;
    }
    if (exact) {
      out.selected = true;
      return true;
    }
    out.obstruction = trace_rebase_obstruction::residual;
  }
  return false;
}
HOLONICS_CALLABLE inline bool discover(
    const trace_rebase_discovery_receipt &ecology, trace_rebase_move move,
    std::uint8_t target, trace_rebase_workspace &workspace,
    trace_rebase_candidate &out) noexcept {
  return discover_filtered(ecology, move, target, workspace, out, 255U);
}

} // namespace holonics::organ::trace_rebase_discovery_detail
