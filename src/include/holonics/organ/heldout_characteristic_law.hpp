#pragma once

#include <holonics/organ/characteristic_matrix_law.hpp>
#include <holonics/organ/trace_law_discovery.hpp>

namespace holonics::organ::heldout_characteristic_detail {

HOLONICS_CALLABLE inline void
predict(const trace_law_organ &organ,
        heldout_characteristic_receipt &out) noexcept {
  if (!organ.checker_founded) {
    out.exclusion = hypergeometry_trace_obstruction::organ_absent;
    return;
  }
  out.predicted_trace = trace_law_detail::predict(
      organ, out.visible[0], out.visible[1], out.visible[2]);
  out.predicted_discriminant = out.predicted_trace * out.predicted_trace - 4;
  out.characteristic[0] = 1;
  out.characteristic[1] = -out.predicted_trace;
  out.characteristic[2] = 1;
  out.predicted_fixed_rank = out.predicted_trace == 2 ? 1 : 0;
  out.prediction_before_comparison = true;
}

HOLONICS_CALLABLE inline void
compare(const trace_law_organ &organ, const heldout_local_system_card &card,
        heldout_characteristic_receipt &out) noexcept {
  out.exclusion = hypergeometry_trace_obstruction::organ_absent;
  out.ablation_exact = true;
  auto changed = card;
  auto *slot = changed.edges[0].value;
  slot[changed.changed_slot] = changed.changed_value;
  heldout_characteristic_receipt foil{};
  characteristic_matrix_detail::heldout_faces(changed, foil);
  const bool determinant_exact =
      elementary_matrix_detail::determinant(foil.first) == 1 &&
      elementary_matrix_detail::determinant(foil.second) == 1;
  out.changed = determinant_exact
                    ? hypergeometry_trace_obstruction::comparison_residual
                    : hypergeometry_trace_obstruction::unsupported_determinant;
  out.improved =
      organ.checker_founded && out.prediction_before_comparison &&
      out.predicted_trace == out.source_trace &&
      out.predicted_discriminant == out.source_trace * out.source_trace - 4;
  out.development_sources_absent = true;
  out.theory_formed =
      out.improved && out.ablation_exact &&
      out.changed == hypergeometry_trace_obstruction::unsupported_determinant;
}

} // namespace holonics::organ::heldout_characteristic_detail
