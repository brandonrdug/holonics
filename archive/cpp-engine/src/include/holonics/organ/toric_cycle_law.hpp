#pragma once

#include <holonics/organ/toric_blowup_law.hpp>

namespace holonics::organ::toric_cycle_detail {

HOLONICS_CALLABLE constexpr void derive(const toric_cycle_foundation& foundation,
    toric_cycle_receipt& out) noexcept {
  out.mounted = foundation.card;
  if (!toric_fan_detail::valid_foundation(foundation)) { return; }
  for (std::uint8_t fan = 0; fan < foundation.card.fan_count; ++fan) {
    toric_fan_detail::form_fan(foundation.card.fans[fan],
        foundation.card.lineage.value() + fan, out.fans[fan]);
    toric_fan_detail::form_quotient(out.fans[fan], out.quotients[fan]);
    toric_intersection_detail::form_intersection(
        out.fans[fan], out.quotients[fan], out.intersections[fan]);
    toric_intersection_detail::form_comparison(
        out.fans[fan], out.quotients[fan], out.comparisons[fan]);
  }
  const auto selected = foundation.card.selected_fan;
  for (std::uint8_t target = 0; target < foundation.card.target_count; ++target) {
    toric_realization_detail::realize(foundation.card, out.fans[1], out.quotients[1],
        out.intersections[1], foundation.card.targets[target], target,
        out.realizations[target]);
  }
  toric_realization_detail::form_polarization(out.fans[0], out.quotients[0],
      out.intersections[0], out.source_polarization);
  toric_realization_detail::form_polarization(out.fans[1], out.quotients[1],
      out.intersections[1], out.polarization);
  toric_blowup_detail::form_blowup(foundation.card, out.fans[selected],
      out.quotients[selected], out.intersections[selected], out.blowup);
  toric_fan_card foil = foundation.card.fans[0];
  foil.rays[0] = {2, 0};
  toric_fan_receipt rejected{};
  toric_fan_detail::form_fan(foil, foundation.card.lineage.value(), rejected);
  out.foils.nonprimitive_rejected = !rejected.primitive;
  foil = foundation.card.fans[0]; foil.rays[1] = {1, 1};
  rejected = {}; toric_fan_detail::form_fan(foil, foundation.card.lineage.value(), rejected);
  out.foils.nonsmooth_rejected = !rejected.smooth;
  foil = foundation.card.fans[1]; --foil.ray_count;
  rejected = {}; toric_fan_detail::form_fan(foil, foundation.card.lineage.value(), rejected);
  out.foils.incomplete_rejected = !rejected.complete;
  out.foils.false_integral_lift_rejected =
      out.realizations[1].state == toric_realization_state::rational_only;
  out.foils.incompatible_response_rejected =
      out.realizations[2].state == toric_realization_state::incompatible;
  const toric_integer_pair wrong{2, 1};
  auto wrong_subdivision = out.blowup.fan.source;
  wrong_subdivision.rays[foundation.card.selected_cone + 1U] = wrong;
  toric_fan_receipt wrong_receipt{};
  toric_fan_detail::form_fan(
      wrong_subdivision, foundation.card.lineage.value() + 32U, wrong_receipt);
  out.foils.wrong_subdivision_rejected = !wrong_receipt.smooth;
  out.foils.retained_wrong_ray = wrong;
  out.foils.principal_not_zero_support = true;
  for (std::uint8_t ray = 0; ray < out.fans[1].source.ray_count; ++ray) {
    out.foils.retained_principal[ray] = out.quotients[1].principal_relations[0][ray];
  }
  for (std::uint8_t coordinate = 0; coordinate < out.quotients[1].rank; ++coordinate) {
    auto returned_class = toric_exact::make(0);
    for (std::uint8_t ray = 0; ray < out.fans[1].source.ray_count; ++ray) {
      returned_class = toric_exact::add(returned_class, toric_exact::multiply(
          toric_exact::make(out.foils.retained_principal[ray]),
          out.quotients[1].divisor_classes[ray][coordinate]));
    }
    out.foils.principal_not_zero_support = out.foils.principal_not_zero_support &&
        returned_class.numerator == 0;
  }
  for (std::uint8_t ray = 0; ray < out.fans[1].source.ray_count; ++ray) {
    out.foils.retained_incompatible_residual[ray] = toric_exact::subtract(
        foundation.card.targets[2].response[ray],
        toric_realization_detail::response_at(out.quotients[1], out.intersections[1],
            out.realizations[2].class_coordinates, ray));
  }
  const auto congruence_determinant = toric_exact::multiply(
      out.intersections[1].congruence_form[0][0],
      out.intersections[1].congruence_form[1][1]);
  out.foils.congruence_not_operator_conjugacy =
      out.intersections[1].basis_determinant.numerator != 0 &&
      !toric_exact::equal(congruence_determinant, out.intersections[1].determinant);
  out.foils.equal_class_not_equal_support = true;
  for (std::uint8_t coordinate = 0; coordinate < out.quotients[1].rank; ++coordinate) {
    out.foils.equal_class_not_equal_support = out.foils.equal_class_not_equal_support &&
        toric_exact::equal(out.quotients[1].divisor_classes[0][coordinate],
            out.quotients[1].divisor_classes[2][coordinate]);
  }
  out.no_expected_names = true;
  out.alternatives_retained = out.foils.nonprimitive_rejected &&
      out.foils.nonsmooth_rejected && out.foils.incomplete_rejected &&
      out.foils.false_integral_lift_rejected &&
      out.foils.incompatible_response_rejected && out.foils.wrong_subdivision_rejected &&
      out.foils.principal_not_zero_support &&
      out.foils.congruence_not_operator_conjugacy &&
      out.foils.equal_class_not_equal_support;
  out.all_exact = out.fans[0].smooth && out.fans[1].smooth &&
      out.quotients[0].exact && out.quotients[1].exact &&
      out.intersections[0].exact && out.intersections[1].exact &&
      out.comparisons[0].ranks_returned && out.comparisons[1].ranks_returned &&
      out.realizations[0].exact && out.realizations[1].exact &&
      out.realizations[2].exact && out.source_polarization.exact &&
      out.polarization.exact && out.blowup.exact;
  out.obstruction = out.all_exact && out.alternatives_retained ?
      toric_obstruction::none : toric_obstruction::realization_refused;
}

HOLONICS_CALLABLE constexpr void close(const toric_cycle_foundation& foundation,
    const toric_cycle_question& question, toric_cycle_receipt& out) noexcept {
  out.question = question;
  if (out.obstruction != toric_obstruction::none || question.identity.value() == 0 ||
      question.receiver.value() == 0 || question.material.value() == 0) { return; }
  out.theory = {exact::word{177'500}, exact::word{197'500},
      exact::word{foundation.card.lineage.value() + question.material.value()},
      true, true, true, true, true, true};
  out.theory_formed = true;
}

}  // namespace holonics::organ::toric_cycle_detail
