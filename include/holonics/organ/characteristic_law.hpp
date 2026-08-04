#pragma once

#include <holonics/organ/characteristic_control_law.hpp>
#include <holonics/organ/characteristic_probe_law.hpp>

namespace holonics::organ {

HOLONICS_CALLABLE constexpr void close_characteristic_inquiry(
    const characteristic_foundation& foundation, const characteristic_question& question,
    characteristic_receipt& receipt) noexcept {
  receipt.question = question;
  receipt.no_expected_eigenvalue = true;
  receipt.no_prime_mode_label = true;
  receipt.no_renderer_source = true;
  if (!characteristic_detail::valid_foundation(foundation) ||
      question.identity.value() == 0 || question.receiver.value() == 0 ||
      question.material.value() == 0) { return; }
  receipt.all_cases_exact = true;
  for (std::uint16_t slot = 0; slot < foundation.case_count; ++slot) {
    const auto& value = receipt.cases[slot];
    receipt.returned_cases = static_cast<std::uint16_t>(
        receipt.returned_cases + (value.exact ? 1U : 0U));
    receipt.repeated_mode_cases = static_cast<std::uint16_t>(receipt.repeated_mode_cases +
        (value.global_discriminant_zero ? 1U : 0U));
    receipt.simple_mode_cases = static_cast<std::uint16_t>(receipt.simple_mode_cases +
        (value.mode_multiplicity == 1 ? 1U : 0U));
    receipt.shape_tour_classes = static_cast<std::uint16_t>(
        receipt.shape_tour_classes + value.shape_tour_classes);
    receipt.all_cases_exact = receipt.all_cases_exact && value.exact &&
        !value.local_transport_singular;
  }
  characteristic_detail::form_scalar_control(receipt.scalar);
  characteristic_detail::form_matrix_control(receipt.matrices);
  characteristic_detail::form_indicial(receipt.indicial);
  receipt.theory = {exact::word{174'400}, exact::word{154'400}, exact::word{154'401},
      exact::word{154'402}, exact::word{154'403}, exact::word{194'400},
      receipt.all_cases_exact, receipt.scalar.exact, receipt.matrices.exact,
      receipt.repeated_mode_cases == 2, receipt.indicial.exact, true};
  receipt.theory_formed = receipt.returned_cases == foundation.case_count &&
      receipt.repeated_mode_cases == 2 && receipt.simple_mode_cases == 14 &&
      receipt.all_cases_exact && receipt.scalar.exact && receipt.matrices.exact &&
      receipt.indicial.exact && receipt.theory.diagonal_factor &&
      receipt.theory.weighted_cycle && receipt.theory.matrix_controls &&
      receipt.theory.discriminants_typed && receipt.theory.gauss_indicial &&
      receipt.theory.lineage_retained;
  receipt.obstruction = receipt.theory_formed ? characteristic_obstruction::none :
      characteristic_obstruction::matrix_control_refused;
}

}  // namespace holonics::organ
