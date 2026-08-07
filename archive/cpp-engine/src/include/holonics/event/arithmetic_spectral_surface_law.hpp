#pragma once

#include <holonics/codec/arithmetic_spectral_face.hpp>
#include <holonics/organ/arithmetic_test_current_law.hpp>

namespace holonics::event {

static_assert(codec::arithmetic_surface_curve_count == organ::arithmetic_curve_count);
static_assert(codec::arithmetic_surface_degree_count == organ::arithmetic_degree_count);

[[nodiscard]] HOLONICS_CALLABLE inline codec::arithmetic_spectral_surface
arithmetic_spectral_surface(const organ::arithmetic_spectral_receipt& inquiry) noexcept {
  codec::arithmetic_spectral_surface out{}; out.passage = inquiry.theory.passage;
  for (std::uint8_t curve = 0; curve < organ::arithmetic_curve_count; ++curve) {
    const auto& source = inquiry.curves[curve]; auto& target = out.curves[curve];
    target.prime = source.source.prime; target.coefficient = source.source.coefficient;
    target.a = source.frobenius.real; target.b = source.frobenius.imaginary;
    for (std::uint8_t degree = 0; degree < organ::arithmetic_degree_count; ++degree) {
      target.counts[degree] = source.fixed_counts[degree];
      target.places[degree] = source.closed_places[degree];
      target.traces[degree] = source.power_traces[degree];
    }
    target.traces[organ::arithmetic_degree_count] =
        source.power_traces[organ::arithmetic_degree_count];
    const organ::gaussian_integer pi{target.a,target.b};
    const organ::gaussian_integer conjugate{target.a,-target.b};
    for (std::uint8_t slot = 0; slot <= organ::arithmetic_degree_count; ++slot) {
      const auto value = organ::arithmetic_test_detail::multiply(
          organ::arithmetic_test_detail::power(pi, slot),
          organ::arithmetic_test_detail::power(conjugate,
            organ::arithmetic_degree_count - slot));
      target.homogeneous[slot][0] = value.real;
      target.homogeneous[slot][1] = value.imaginary;
    }
    out.correspondences_exact = (curve == 0 || out.correspondences_exact) && source.correspondence_exact;
    out.forms_exact = (curve == 0 || out.forms_exact) && source.forms_exact;
    out.traces_exact = (curve == 0 || out.traces_exact) && source.fixed_trace_agrees;
  }
  out.fixed_contributions = inquiry.theory.fixed_contributions;
  out.candidate_count = inquiry.theory.correspondence_candidates;
  out.point_count = inquiry.theory.correspondence_points;
  out.trace_current_count = inquiry.theory.trace_currents;
  out.norm_current_count = inquiry.theory.norm_currents;
  out.rechart_scale = inquiry.controls.rechart_scale;
  out.fields_exact = inquiry.towers[0].exact && inquiry.towers[1].exact;
  out.controls_exact = inquiry.controls.twist_5_exact && inquiry.controls.twist_13_exact &&
      inquiry.controls.changed_twist_exact && inquiry.controls.even_counts_preserved &&
      inquiry.controls.odd_counts_reversed && inquiry.controls.equal_factor_rechart &&
      inquiry.controls.gaussian_phase_separated && inquiry.controls.source_lineage_retained;
  out.archimedean_inapplicable = inquiry.controls.archimedean_inapplicable;
  out.alternatives_retained = inquiry.alternatives_retained; return out;
}

}  // namespace holonics::event
