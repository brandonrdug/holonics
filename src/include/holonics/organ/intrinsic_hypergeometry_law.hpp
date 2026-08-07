#pragma once

#include <holonics/organ/intrinsic_control_law.hpp>

namespace holonics::organ::intrinsic_hypergeometry_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const intrinsic_hypergeometry_foundation& value) noexcept {
  return value.ecology.value() != 0 && value.incidence.value() != 0 &&
      value.chronology.value() != 0 && value.receiver.value() != 0 &&
      value.local_system.value() != 0 && value.characteristic.value() != 0 &&
      value.theorem.value() != 0 && value.provenance.value() != 0 &&
      valid_card(value.card) && cm_incidence_detail::valid_card(value.cm) &&
      value.variation.parsed;
}

HOLONICS_CALLABLE constexpr void derive_phase(
    const intrinsic_hypergeometry_foundation& foundation, std::uint8_t slot,
    intrinsic_hypergeometry_receipt& out) noexcept {
  if (slot == 0) { out.mounted = foundation.card; }
  if (!valid_foundation(foundation) || slot >= intrinsic_case_capacity) { return; }
  derive_phase_incidence(foundation, slot, out.cases[slot]);
}

HOLONICS_CALLABLE constexpr void derive_variation(
    const intrinsic_hypergeometry_foundation& foundation,
    intrinsic_hypergeometry_receipt& out) noexcept {
  if (!valid_foundation(foundation)) { return; }
  derive_section_source(foundation, out.series, out.local_system);
}

HOLONICS_CALLABLE constexpr void derive_cm(
    const intrinsic_hypergeometry_foundation& foundation,
    intrinsic_hypergeometry_receipt& out) noexcept {
  if (!valid_foundation(foundation)) { return; }
  derive_supported_cycles(foundation, out.supported);
}

HOLONICS_CALLABLE constexpr void carry_phase(
    const intrinsic_hypergeometry_foundation& foundation, std::uint8_t slot,
    intrinsic_hypergeometry_receipt& out) noexcept {
  if (!valid_foundation(foundation) || slot >= intrinsic_case_capacity) { return; }
  form_chronology(foundation, out.local_system, out.cases[slot]);
}

HOLONICS_CALLABLE constexpr void close(
    const intrinsic_hypergeometry_foundation& foundation,
    intrinsic_hypergeometry_question question,
    intrinsic_hypergeometry_receipt& out) noexcept {
  out.question = question; out.no_expected_invariants = true;
  if (!valid_foundation(foundation) || question.identity.value() == 0 ||
      question.receiver.value() == 0 || question.material.value() == 0) {
    out.obstruction = intrinsic_hypergeometry_obstruction::invalid_foundation; return;
  }
  compose_supported_cycles(out.local_system, out.supported);
  out.source_mask = 0;
  for (std::uint8_t slot = 0; slot < intrinsic_case_capacity; ++slot) {
    if (out.cases[slot].exact) { out.source_mask |= static_cast<std::uint16_t>(1U << slot); }
  }
  if (out.series.recurrence_exact && out.local_system.exact) { out.source_mask |= 1U << 10U; }
  if (out.supported.exact) { out.source_mask |= 1U << 11U; }
  if (out.source_mask != 0x0fffU) {
    out.obstruction = intrinsic_hypergeometry_obstruction::composition_refused; return;
  }
  derive_controls(foundation, out);
  out.source_currents_independent = out.cases[0].identity != out.cases[1].identity &&
      out.series.identity != out.supported.identity &&
      out.cases[0].identity != out.series.identity &&
      out.cases[0].identity != out.supported.identity;
  out.alternatives_retained = out.local_system.alternatives_unequal &&
      out.supported.filled_extension_obstructed &&
      out.supported.supported_loop_admitted;
  out.theory = {exact::word{193'600}, exact::word{193'601},
      exact::word{foundation.card.lineage.value() + question.material.value()},
      out.source_mask, true, true, true, out.supported.exact, out.controls.exact};
  out.all_exact = out.source_currents_independent && out.no_expected_invariants &&
      out.alternatives_retained && out.controls.exact;
  out.theory_formed = out.all_exact && out.theory.source_mask == 0x0fffU &&
      out.theory.incidence_exact && out.theory.distributions_exact &&
      out.theory.sections_exact && out.theory.supported_cycles_exact &&
      out.theory.controls_exact;
  out.obstruction = out.theory_formed ? intrinsic_hypergeometry_obstruction::none :
      intrinsic_hypergeometry_obstruction::control_refused;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr intrinsic_hypergeometry_receipt derive(
    const intrinsic_hypergeometry_foundation& foundation,
    intrinsic_hypergeometry_question question) noexcept {
  intrinsic_hypergeometry_receipt out{};
  for (std::uint8_t slot = 0; slot < intrinsic_case_capacity; ++slot) {
    derive_phase(foundation, slot, out);
  }
  derive_variation(foundation, out); derive_cm(foundation, out);
  for (std::uint8_t slot = 0; slot < intrinsic_case_capacity; ++slot) {
    carry_phase(foundation, slot, out);
  }
  close(foundation, question, out); return out;
}

}  // namespace holonics::organ::intrinsic_hypergeometry_detail
