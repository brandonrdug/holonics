#pragma once

#include <holonics/organ/causal_linear_control_law.hpp>

namespace holonics::organ::causal_linear_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const causal_linear_foundation& value) noexcept {
  return value.ecology.value() != 0 && value.matrix.value() != 0 &&
      value.chain.value() != 0 && value.characteristic.value() != 0 &&
      value.multilinear.value() != 0 && value.coefficient_field.value() != 0 &&
      value.theorem.value() != 0 && value.provenance.value() != 0 &&
      value.card.parsed && value.card.schema.value() == 250'025 &&
      value.card.occurrence.value() != 0 && value.card.phase_first >= 2 &&
      value.card.phase_second >= 2 && value.card.eigen_min <= -2 &&
      value.card.eigen_max >= 2 && cm_incidence_detail::valid_card(value.cm) &&
      value.toric.parsed && value.variation.parsed;
}

HOLONICS_CALLABLE constexpr void derive_source(const causal_linear_foundation& foundation,
    std::uint8_t source, causal_linear_receipt& out) noexcept {
  if (source == 0) { out.mounted = foundation.card; }
  if (!valid_foundation(foundation)) { return; }
  if (source == 0) { derive_phase(foundation.card, out.phase); }
  else if (source == 1) { derive_cm(foundation.cm, out.cm); }
  else if (source == 2) { derive_toric(foundation.toric, out.toric); }
  else if (source == 3) { derive_variation(foundation.variation, out.variation); }
}

HOLONICS_CALLABLE constexpr void close(const causal_linear_foundation& foundation,
    causal_linear_question question, causal_linear_receipt& out) noexcept {
  out.question = question; out.no_expected_invariants = true;
  if (!valid_foundation(foundation) || question.identity.value() == 0 ||
      question.receiver.value() == 0 || question.material.value() == 0) {
    out.obstruction = causal_linear_obstruction::invalid_foundation; return;
  }
  out.source_mask = static_cast<std::uint8_t>((out.phase.exact ? 1U : 0U) |
      (out.cm.exact ? 2U : 0U) | (out.toric.exact ? 4U : 0U) |
      (out.variation.exact ? 8U : 0U));
  if (out.source_mask != 15) {
    out.obstruction = causal_linear_obstruction::source_refused; return;
  }
  close_controls(out.controls);
  out.source_sections_independent = out.phase.identity != out.cm.identity &&
      out.phase.identity != out.toric.identity && out.phase.identity != out.variation.identity &&
      out.cm.identity != out.toric.identity && out.cm.identity != out.variation.identity &&
      out.toric.identity != out.variation.identity;
  out.alternatives_retained = out.controls.equal_characteristic_unequal_fixed &&
      out.controls.unequal_kernel_placement && out.controls.rational_eigenvalue_absent &&
      out.toric.topology_changed;
  out.theory = {exact::word{192'600}, exact::word{192'601},
      exact::word{foundation.card.lineage.value() + question.material.value()}, out.source_mask,
      true, out.phase.boundary_composite_zero, true,
      out.variation.exterior_exact && out.variation.tensor.exact, out.controls.exact};
  out.all_exact = out.source_mask == 15 && out.source_sections_independent &&
      out.alternatives_retained && out.no_expected_invariants && out.controls.exact;
  out.theory_formed = out.all_exact && out.theory.source_mask == 15 &&
      out.theory.matrices_exact && out.theory.chains_exact &&
      out.theory.characteristics_exact && out.theory.multilinear_exact &&
      out.theory.controls_exact;
  out.obstruction = out.theory_formed ? causal_linear_obstruction::none :
      causal_linear_obstruction::aggregation_refused;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr causal_linear_receipt derive(
    const causal_linear_foundation& foundation,
    causal_linear_question question) noexcept {
  causal_linear_receipt out{};
  for (std::uint8_t source = 0; source < 4; ++source) {
    derive_source(foundation, source, out);
  }
  derive_controls(foundation.card, out.controls);
  close(foundation, question, out); return out;
}

}  // namespace holonics::organ::causal_linear_detail
