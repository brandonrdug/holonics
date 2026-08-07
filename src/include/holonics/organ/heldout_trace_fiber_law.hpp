#pragma once

#include <holonics/organ/trace_fiber_discovery_law.hpp>
#include <holonics/organ/trace_fiber_matrix_law.hpp>

namespace holonics::organ {

struct heldout_trace_fiber_receipt final {
  exact_matrix2 matrices[8]{};
  std::int64_t lower[trace_fiber_lower_count]{};
  std::int64_t anchor{};
  std::int64_t predicted_companion{};
  std::int64_t source_companion{};
  std::int64_t symmetric[2]{};
  std::int64_t quadratic[3]{};
  std::int64_t roots[2]{};
  std::int64_t discriminant{};
  std::int64_t root_gap{};
  trace_fiber_obstruction exclusion{trace_fiber_obstruction::none};
  trace_fiber_obstruction orientation_exclusion{trace_fiber_obstruction::none};
  trace_fiber_obstruction changed{trace_fiber_obstruction::none};
  exact::word passage{};
  exact::word lineage{};
  bool development_sources_absent{};
  bool prediction_before_comparison{};
  bool unordered_without_orientation{};
  bool improved{};
  bool theory_formed{};
};

} // namespace holonics::organ

namespace holonics::organ::heldout_trace_fiber_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
square_root(std::int64_t value) noexcept {
  if (value < 0)
    return -1;
  if (value == 0)
    return 0;
  std::uint64_t low = 0;
  std::uint64_t high = static_cast<std::uint64_t>(value) < 3'037'000'499ULL
                           ? static_cast<std::uint64_t>(value)
                           : 3'037'000'499ULL;
  const auto target = static_cast<std::uint64_t>(value);
  while (low <= high) {
    const auto mid = low + ((high - low) >> 1U);
    if (mid == 0) {
      low = 1;
      continue;
    }
    const auto square = mid * mid;
    if (square == target)
      return static_cast<std::int64_t>(mid);
    if (square < target)
      low = mid + 1U;
    else {
      if (mid == 0)
        break;
      high = mid - 1U;
    }
  }
  return -1;
}
HOLONICS_CALLABLE inline void expose(
    const trace_fiber_matrix_detail::heldout_trace_source_secret &source,
    heldout_trace_fiber_receipt &out) noexcept {
  out = {};
  for (std::uint8_t i = 0; i < trace_fiber_lower_count; ++i)
    out.lower[i] = source.lower[i];
  out.anchor = source.ordered[0];
  out.lineage = source.lineage;
  out.development_sources_absent = true;
}
HOLONICS_CALLABLE inline void predict(const trace_fiber_organ &sum,
                                      const trace_fiber_organ &product,
                                      heldout_trace_fiber_receipt &out) noexcept {
  if (!trace_fiber_discovery_detail::predict(sum, out.lower,
                                              out.symmetric[0]) ||
      !trace_fiber_discovery_detail::predict(product, out.lower,
                                              out.symmetric[1])) {
    out.exclusion = trace_fiber_obstruction::organ_absent;
    return;
  }
  out.quadratic[0] = 1;
  out.quadratic[1] = -out.symmetric[0];
  out.quadratic[2] = out.symmetric[1];
  out.discriminant = out.symmetric[0] * out.symmetric[0] -
                     4 * out.symmetric[1];
  if (out.discriminant < 0) {
    out.exclusion = trace_fiber_obstruction::negative_discriminant;
    return;
  }
  out.root_gap = square_root(out.discriminant);
  if (out.root_gap < 0) {
    out.exclusion = trace_fiber_obstruction::nonsquare_discriminant;
    return;
  }
  out.roots[0] = (out.symmetric[0] - out.root_gap) / 2;
  out.roots[1] = (out.symmetric[0] + out.root_gap) / 2;
  out.predicted_companion = out.symmetric[0] - out.anchor;
  out.prediction_before_comparison =
      (out.anchor == out.roots[0] || out.anchor == out.roots[1]) &&
      (out.predicted_companion == out.roots[0] ||
       out.predicted_companion == out.roots[1]);
  auto unoriented = out;
  unoriented.orientation_exclusion = trace_fiber_obstruction::orientation_unresolved;
  unoriented.predicted_companion = 0;
  out.unordered_without_orientation =
      unoriented.roots[0] == out.roots[0] &&
      unoriented.roots[1] == out.roots[1] &&
      unoriented.orientation_exclusion ==
          trace_fiber_obstruction::orientation_unresolved;
  out.orientation_exclusion = unoriented.orientation_exclusion;
}
HOLONICS_CALLABLE inline void compare(
    const trace_fiber_organ &sum, const trace_fiber_organ &product,
    const heldout_oriented_system_card &card,
    const trace_fiber_matrix_detail::heldout_trace_source_secret &source,
    heldout_trace_fiber_receipt &out) noexcept {
  for (std::uint8_t i = 0; i < 8; ++i)
    out.matrices[i] = source.matrices[i];
  out.source_companion = source.ordered[1];
  out.improved = out.prediction_before_comparison &&
                 out.predicted_companion == out.source_companion;
  trace_fiber_organ absent = sum;
  absent.primitive = false;
  std::int64_t discarded = 0;
  out.exclusion = trace_fiber_discovery_detail::predict(absent, out.lower,
                                                         discarded)
                      ? trace_fiber_obstruction::comparison_residual
                      : trace_fiber_obstruction::organ_absent;
  auto changed = source.matrices[card.changed_matrix];
  changed.value[card.changed_slot] = card.changed_value;
  out.changed = elementary_matrix_detail::determinant(changed) == 1
                    ? trace_fiber_obstruction::comparison_residual
                    : trace_fiber_obstruction::unsupported_determinant;
  out.theory_formed = out.improved && out.unordered_without_orientation &&
                      out.exclusion == trace_fiber_obstruction::organ_absent &&
                      out.changed == trace_fiber_obstruction::unsupported_determinant &&
                      sum.checker_founded && product.checker_founded;
}

} // namespace holonics::organ::heldout_trace_fiber_detail
