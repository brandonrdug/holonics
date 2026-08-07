#pragma once

#include <holonics/organ/regular_singular_connection_law.hpp>
#include <holonics/organ/regular_singular_probe_law.hpp>

namespace holonics::organ {

HOLONICS_CALLABLE constexpr void close_regular_singular_inquiry(
    const regular_singular_foundation& foundation,
    const regular_singular_question& question,
    regular_singular_receipt& receipt) noexcept {
  receipt.question = question;
  receipt.mounted_operator = foundation.mounted_operator;
  receipt.no_special_function_lookup = true;
  receipt.no_numerical_continuation = true;
  receipt.no_expected_logarithm = true;
  receipt.no_expected_eigenvector = true;
  if (!regular_singular_detail::valid_foundation(foundation) ||
      question.identity.value() == 0 || question.receiver.value() == 0 ||
      question.material.value() == 0) { return; }
  receipt.system = regular_singular_detail::derive_system(foundation.mounted_operator);
  receipt.all_exact = receipt.system.derived;
  for (std::size_t slot = 0; slot < regular_singular_chart_capacity; ++slot) {
    const auto& chart = receipt.charts[slot];
    receipt.returned_charts = static_cast<std::uint16_t>(
        receipt.returned_charts + (chart.exact ? 1U : 0U));
    receipt.logarithmic_charts = static_cast<std::uint16_t>(
        receipt.logarithmic_charts + (chart.logarithmic_channel ? 1U : 0U));
    receipt.all_exact = receipt.all_exact && chart.exact;
  }
  for (std::size_t slot = 0; slot < foundation.term_count; ++slot) {
    const auto& term = receipt.terms[slot];
    receipt.returned_terms = static_cast<std::uint16_t>(
        receipt.returned_terms + (term.exact ? 1U : 0U));
    receipt.all_exact = receipt.all_exact && term.exact;
  }
  regular_singular_detail::form_connection(foundation, receipt.connection);
  receipt.theory = {exact::word{175'400}, exact::word{155'400}, exact::word{155'401},
      exact::word{155'402}, exact::word{155'403},
      exact::word{receipt.connection.loop_lineage},
      receipt.system.derived, receipt.returned_terms == foundation.term_count,
      receipt.charts[1].obstruction_scalar == 1,
      receipt.connection.conjugacy_exact,
      receipt.connection.punctured_sphere_product_exact, true};
  receipt.theory_formed = receipt.returned_charts == regular_singular_chart_capacity &&
      receipt.returned_terms == foundation.term_count && receipt.logarithmic_charts == 2 &&
      receipt.all_exact && receipt.connection.exact && receipt.theory.residue_algebra &&
      receipt.theory.frobenius_steps && receipt.theory.resonance_obstruction &&
      receipt.theory.chamber_connection && receipt.theory.loop_product &&
      receipt.theory.lineage_retained;
  receipt.obstruction = receipt.theory_formed ? regular_singular_obstruction::none :
      regular_singular_obstruction::connection_refused;
}

}  // namespace holonics::organ
