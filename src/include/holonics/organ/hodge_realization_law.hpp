#pragma once

#include <holonics/organ/hodge_blowup_law.hpp>

namespace holonics::organ::hodge_realization_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_foundation(
    const hodge_realization_foundation& foundation) noexcept {
  const auto& card = foundation.card;
  if (!card.parsed || card.schema != exact::word{280'028} || card.factor_count != 2 ||
      card.rank != 6 || card.question_count != 3 || card.base_t != 2 || card.base_u != 2 ||
      card.off_diagonal_u != 3 || card.coefficient_min != -1 || card.coefficient_max != 1 ||
      card.denominator_aperture != 2 || card.center_selector >= 4 ||
      card.changed_center_selector >= 4 || card.center_selector == card.changed_center_selector) {
    return false;
  }
  for (const auto& factor : card.factors) {
    if (!factor.exact || factor.term_count != 5) { return false; }
  }
  for (const auto& target : card.questions) {
    if (target.denominator == 0 || target.denominator > card.denominator_aperture) { return false; }
  }
  return foundation.ecology.value() != 0 && foundation.family.value() != 0 &&
      foundation.cohomology.value() != 0 && foundation.filtration.value() != 0 &&
      foundation.transport.value() != 0 && foundation.cycle.value() != 0 &&
      foundation.blowup.value() != 0 && foundation.theorem.value() != 0 &&
      foundation.provenance.value() != 0;
}

HOLONICS_CALLABLE constexpr void close(hodge_realization_receipt& out,
    const hodge_blowup_receipt& changed) noexcept {
  const bool center_changed = changed.exact && out.blowup.center_selector !=
      changed.center_selector && out.blowup.through_center[out.blowup.center_selector] &&
      changed.through_center[changed.center_selector] &&
      !changed.through_center[out.blowup.center_selector];
  out.no_expected_invariants = true;
  out.alternatives_retained = out.cycles.alternatives_retained &&
      out.cycles.fibers[2].outside_image && center_changed;
  out.theory = {exact::word{195'620}, exact::word{195'621},
      exact::word{out.mounted.lineage.value() + 384U}, out.factors[0].exact && out.factors[1].exact,
      out.product.exact, out.cycles.locus.exact, out.cycles.exact,
      out.blowup.exact && changed.exact};
  out.obstruction = hodge_realization_obstruction::none;
  out.all_exact = out.theory.families_exact && out.theory.cohomology_exact &&
      out.theory.filtration_exact && out.theory.cycles_exact && out.theory.blowup_exact &&
      out.no_expected_invariants && out.alternatives_retained;
  out.theory_formed = out.all_exact;
  if (!out.theory_formed) { out.obstruction = hodge_realization_obstruction::realization_refused; }
}

}  // namespace holonics::organ::hodge_realization_detail
