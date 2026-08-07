#pragma once

#include <holonics/organ/arithmetic_test_current_law.hpp>

namespace holonics::organ::arithmetic_realization_detail {

HOLONICS_CALLABLE inline void close(arithmetic_spectral_receipt& out) noexcept {
  out.all_exact = out.towers[0].exact && out.towers[1].exact;
  for (const auto& curve : out.curves) { out.all_exact = out.all_exact && curve.exact; }
  arithmetic_spectral_detail::form_controls(out);
  out.all_exact = out.all_exact && out.controls.twist_5_exact && out.controls.twist_13_exact &&
      out.controls.changed_twist_exact && out.controls.even_counts_preserved &&
      out.controls.odd_counts_reversed && out.controls.equal_factor_rechart &&
      out.controls.gaussian_phase_separated && out.controls.source_lineage_retained &&
      out.controls.archimedean_inapplicable;
  if (!out.all_exact) { out.obstruction = arithmetic_spectral_obstruction::trace_refused; return; }
  out.theory.identity = exact::word{196'410}; out.theory.passage = exact::word{196'411};
  out.theory.lineage = exact::word{out.controls.lineage.value() + 1U};
  out.theory.fixed_contributions = arithmetic_fixed_capacity;
  out.theory.correspondence_candidates = arithmetic_curve_count * arithmetic_candidate_count;
  std::uint32_t points = 0;
  for (const auto& curve : out.curves) { points += curve.pointwise_points; }
  out.theory.correspondence_points = points;
  out.theory.trace_currents = arithmetic_curve_count * arithmetic_trace_current_count;
  out.theory.norm_currents = arithmetic_curve_count * arithmetic_norm_current_count;
  out.theory.complete = true; out.theory_formed = true;
}

}  // namespace holonics::organ::arithmetic_realization_detail
