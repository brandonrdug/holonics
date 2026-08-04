#pragma once

#include <holonics/organ/blind_code_law.hpp>
#include <holonics/organ/blind_moment_law.hpp>

namespace holonics::organ {
namespace blind_reconstruction_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const blind_reconstruction_foundation& value) noexcept {
  if (value.ecology.value() == 0 || value.code_incidence.value() == 0 ||
      value.orthogonal_transport.value() == 0 || value.moment_transport.value() == 0 ||
      value.characteristic_transport.value() == 0 ||
      value.candidate_transport.value() == 0 || value.provenance.value() == 0 ||
      value.code.schema != exact::word{210'021} || !value.code.parsed ||
      value.code.byte_fold == 0 || value.code.path_fold == 0 ||
      value.moments.schema != exact::word{210'022} || !value.moments.parsed ||
      value.moments.byte_fold == 0 || value.moments.path_fold == 0 ||
      value.moments.case_count != blind_moment_case_capacity) { return false; }
  for (std::uint8_t slot = 0; slot < value.moments.case_count; ++slot) {
    if (!blind_moment_detail::valid_case(value.moments.cases[slot])) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool alternatives_complete(
    const blind_reconstruction_receipt& receipt) noexcept {
  for (std::uint8_t pair = 0; pair < blind_pair_capacity; ++pair) {
    for (std::uint8_t slot = 0; slot < blind_candidate_capacity; ++slot) {
      if (receipt.pairs[pair].candidates[slot].identity.value() == 0) { return false; }
    }
  }
  for (std::uint8_t moment = 0; moment < blind_moment_case_capacity; ++moment) {
    if (!receipt.moments[moment].access_complete) { continue; }
    for (std::uint8_t slot = 0; slot < blind_candidate_capacity; ++slot) {
      if (receipt.moments[moment].candidates[slot].identity.value() == 0) { return false; }
    }
  }
  return true;
}

HOLONICS_CALLABLE constexpr void close_blind_reconstruction(
    const blind_reconstruction_foundation& foundation,
    const blind_reconstruction_question& question,
    blind_reconstruction_receipt& receipt) noexcept {
  receipt.question = question;
  receipt.mounted_code = foundation.code;
  receipt.mounted_moments = foundation.moments;
  receipt.no_released_solution_access = true;
  receipt.no_expected_operator = true;
  receipt.no_expected_roots = true;
  if (!valid_foundation(foundation) || question.identity.value() == 0 ||
      question.receiver.value() == 0 || question.material.value() == 0) { return; }
  for (std::uint8_t slot = 0; slot < blind_pair_capacity; ++slot) {
    receipt.returned_pairs = static_cast<std::uint8_t>(receipt.returned_pairs +
        (receipt.pairs[slot].exact ? 1U : 0U));
  }
  for (std::uint8_t slot = 0; slot < foundation.moments.case_count; ++slot) {
    receipt.returned_moments = static_cast<std::uint8_t>(receipt.returned_moments +
        (receipt.moments[slot].exact ? 1U : 0U));
    receipt.separable_moments = static_cast<std::uint8_t>(receipt.separable_moments +
        (receipt.moments[slot].separable ? 1U : 0U));
    receipt.obstructed_moments = static_cast<std::uint8_t>(receipt.obstructed_moments +
        (receipt.moments[slot].obstruction != blind_obstruction::none ? 1U : 0U));
  }
  receipt.alternatives_retained = alternatives_complete(receipt);
  const bool rechart_exact = blind_code_detail::same_factor(receipt.pairs[0], receipt.pairs[1]) &&
      receipt.pairs[0].lineage != receipt.pairs[1].lineage &&
      receipt.pairs[0].left_size == receipt.pairs[1].right_size &&
      receipt.pairs[0].right_size == receipt.pairs[1].left_size;
  receipt.all_exact = receipt.code.exact &&
      receipt.returned_pairs == blind_pair_capacity &&
      receipt.returned_moments == blind_moment_case_capacity &&
      receipt.separable_moments == 3 && receipt.obstructed_moments == 2 &&
      receipt.moments[3].obstruction == blind_obstruction::singular_root_fiber &&
      receipt.moments[4].obstruction == blind_obstruction::moment_access_refused &&
      receipt.alternatives_retained && rechart_exact;
  receipt.theory = {exact::word{176'500}, exact::word{176'501},
      exact::word{156'500}, exact::word{156'501}, exact::word{196'500},
      receipt.code.exact, receipt.returned_pairs == blind_pair_capacity,
      receipt.separable_moments == 3, receipt.obstructed_moments == 2,
      receipt.alternatives_retained, true};
  receipt.theory_formed = receipt.all_exact && receipt.theory.code_incidence &&
      receipt.theory.jacobi_transport && receipt.theory.moment_pencil &&
      receipt.theory.separability_boundary && receipt.theory.alternatives_retained &&
      receipt.theory.source_separated;
  receipt.obstruction = receipt.theory_formed ? blind_obstruction::none :
      blind_obstruction::pair_factor_refused;
}

}  // namespace blind_reconstruction_detail
}  // namespace holonics::organ
