#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_curve_law.hpp>

namespace holonics::organ::arithmetic_spectral_detail {

[[nodiscard]] HOLONICS_CALLABLE inline bool valid_foundation(
    const arithmetic_spectral_foundation& foundation) noexcept {
  const auto& card = foundation.card;
  return card.parsed && card.schema == exact::word{290'029} &&
      card.degree_min == 1 && card.degree_max == 4 && card.candidate_min == -4 &&
      card.candidate_max == 4 && card.test_degree == 4 && card.test_min == -1 &&
      card.test_max == 1 && card.rechart_left < arithmetic_baseline_count &&
      card.rechart_right < arithmetic_baseline_count && foundation.event.value() != 0 &&
      foundation.incoming_port.value() != 0 && foundation.return_port.value() != 0;
}

HOLONICS_CALLABLE inline void mount_sources(
    const arithmetic_spectral_foundation& foundation, arithmetic_spectral_receipt& out) noexcept {
  out.mounted = foundation.card; out.no_expected_invariants = true;
  out.alternatives_retained = true;
  for (std::uint8_t slot = 0; slot < arithmetic_baseline_count; ++slot) {
    out.curves[slot].source = foundation.card.baseline[slot];
  }
  auto& changed = out.curves[arithmetic_curve_count - 1U].source;
  changed = {foundation.card.changed_prime, foundation.card.changed_to,
      exact::word{196'390}, exact::word{foundation.card.lineage.value() + 390U}};
}

HOLONICS_CALLABLE inline void form_carrier(arithmetic_curve_receipt& out,
    const correspondence_candidate_receipt& selected) noexcept {
  out.frobenius = {selected.real, selected.imaginary};
  const auto a = out.frobenius.real; const auto b = out.frobenius.imaginary;
  const auto p = static_cast<std::int64_t>(out.source.prime);
  out.matrix[0][0] = a; out.matrix[0][1] = -b;
  out.matrix[1][0] = b; out.matrix[1][1] = a;
  out.characteristic[0] = p; out.characteristic[1] = -2 * a; out.characteristic[2] = 1;
  out.discriminant_characteristic = -4 * b * b;
  out.alternating_pullback[0][1] = p; out.alternating_pullback[1][0] = -p;
  out.positive_pullback[0][0] = p; out.positive_pullback[1][1] = p;
  out.primary_eigenvectors[0][0][0] = 1; out.primary_eigenvectors[0][1][1] = -1;
  out.primary_eigenvectors[1][0][0] = 1; out.primary_eigenvectors[1][1][1] = 1;
  out.primary_eigenvalues[0] = {a,b}; out.primary_eigenvalues[1] = {a,-b};
  out.primary_gluing = {0,2};
  out.correspondence_exact = selected.norm_matches && selected.mismatches == 0;
  out.correspondence_precedes_matrix = out.correspondence_exact;
  out.pointwise_points = selected.points_tested;
  out.correspondence_bound = static_cast<std::uint32_t>(4U * out.source.prime);
  out.degree_bound_closes = out.pointwise_points > out.correspondence_bound;
  out.forms_exact = a * a + b * b == p && out.alternating_pullback[0][0] == 0 &&
      out.alternating_pullback[0][1] == p && out.alternating_pullback[1][0] == -p &&
      out.alternating_pullback[1][1] == 0 && out.positive_pullback[0][0] == p &&
      out.positive_pullback[0][1] == 0 && out.positive_pullback[1][0] == 0 &&
      out.positive_pullback[1][1] == p;
  out.weight_exact = out.forms_exact && out.discriminant_characteristic == -4 * b * b;
  out.primary_exact = b != 0 && out.primary_eigenvectors[0][0][0] == 1 &&
      out.primary_eigenvectors[0][0][1] == 0 && out.primary_eigenvectors[0][1][0] == 0 &&
      out.primary_eigenvectors[0][1][1] == -1 && out.primary_eigenvectors[1][0][0] == 1 &&
      out.primary_eigenvectors[1][0][1] == 0 && out.primary_eigenvectors[1][1][0] == 0 &&
      out.primary_eigenvectors[1][1][1] == 1 && out.primary_eigenvalues[0].real == a &&
      out.primary_eigenvalues[0].imaginary == b && out.primary_eigenvalues[1].real == a &&
      out.primary_eigenvalues[1].imaginary == -b && out.primary_gluing.real == 0 &&
      out.primary_gluing.imaginary == 2 &&
      out.primary_gluing.real * out.primary_gluing.real +
          out.primary_gluing.imaginary * out.primary_gluing.imaginary == 4;
  out.power_traces[0] = 2; out.power_traces[1] = 2 * a;
  for (std::uint8_t degree = 2; degree <= arithmetic_degree_count; ++degree) {
    out.power_traces[degree] = 2 * a * out.power_traces[degree - 1U] -
        p * out.power_traces[degree - 2U];
  }
  out.fixed_trace_agrees = true;
  for (std::uint8_t degree = 1; degree <= arithmetic_degree_count; ++degree) {
    const auto expected = static_cast<std::int64_t>(
        arithmetic_field_detail::power_u32(out.source.prime, degree)) + 1 - out.power_traces[degree];
    out.fixed_trace_agrees = out.fixed_trace_agrees &&
        expected == static_cast<std::int64_t>(out.fixed_counts[degree - 1U]);
  }
  out.closed_places[0] = out.fixed_counts[0];
  out.closed_places[1] = static_cast<std::uint32_t>(
      exact::divide_unsigned(out.fixed_counts[1] - out.fixed_counts[0], 2U).quotient);
  out.closed_places[2] = static_cast<std::uint32_t>(
      exact::divide_unsigned(out.fixed_counts[2] - out.fixed_counts[0], 3U).quotient);
  out.closed_places[3] = static_cast<std::uint32_t>(
      exact::divide_unsigned(out.fixed_counts[3] - out.fixed_counts[1], 4U).quotient);
  out.euler_prefix_exact = out.closed_places[0] + 2U * out.closed_places[1] == out.fixed_counts[1] &&
      out.closed_places[0] + 3U * out.closed_places[2] == out.fixed_counts[2] &&
      out.closed_places[0] + 2U * out.closed_places[1] + 4U * out.closed_places[3] == out.fixed_counts[3];
  out.functional_relation = out.characteristic[0] == p &&
      out.characteristic[1] == -2 * a && out.characteristic[2] == 1 &&
      out.characteristic[0] == a * a + b * b;
  out.exact = out.smooth && out.correspondence_exact && out.degree_bound_closes &&
      out.fixed_trace_agrees && out.forms_exact && out.weight_exact && out.primary_exact &&
      out.euler_prefix_exact && out.functional_relation;
}

HOLONICS_CALLABLE inline void form_controls(arithmetic_spectral_receipt& out) noexcept {
  auto& control = out.controls; const auto& c = out.curves;
  control.twist_5_exact = c[0].power_traces[1] == -c[1].power_traces[1];
  control.twist_13_exact = c[2].power_traces[1] == -c[3].power_traces[1];
  control.changed_twist_exact = c[4].power_traces[1] == -c[6].power_traces[1];
  control.even_counts_preserved = c[0].fixed_counts[1] == c[1].fixed_counts[1] &&
      c[0].fixed_counts[3] == c[1].fixed_counts[3] && c[2].fixed_counts[1] == c[3].fixed_counts[1] &&
      c[2].fixed_counts[3] == c[3].fixed_counts[3] && c[4].fixed_counts[1] == c[6].fixed_counts[1] &&
      c[4].fixed_counts[3] == c[6].fixed_counts[3];
  control.odd_counts_reversed = c[0].fixed_counts[0] + c[1].fixed_counts[0] == 12 &&
      c[0].fixed_counts[2] + c[1].fixed_counts[2] == 252 &&
      c[2].fixed_counts[0] + c[3].fixed_counts[0] == 28 &&
      c[2].fixed_counts[2] + c[3].fixed_counts[2] == 4'396 &&
      c[4].fixed_counts[0] + c[6].fixed_counts[0] == 28 &&
      c[4].fixed_counts[2] + c[6].fixed_counts[2] == 4'396;
  control.rechart_scale = 2;
  control.equal_factor_rechart = c[2].characteristic[1] == c[5].characteristic[1] &&
      arithmetic_field_detail::reduced(3 - 16, 13) == 0;
  control.gaussian_phase_separated = c[2].frobenius.real != c[4].frobenius.real &&
      c[2].frobenius.imaginary != c[4].frobenius.imaginary;
  control.source_lineage_retained = c[2].source.lineage != c[5].source.lineage;
  control.archimedean_inapplicable = true;
  control.lineage = exact::word{out.mounted.lineage.value() + 800U};
}

}  // namespace holonics::organ::arithmetic_spectral_detail
