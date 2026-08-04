#pragma once

#include <holonics/organ/theorem_production_receipt.hpp>

namespace holonics::organ {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_theorem_foundation(
    const theorem_production_foundation& value) noexcept {
  if (value.ecology.value() == 0 || value.trace_declaration.value() == 0 ||
      value.trace_trans_declaration.value() == 0 || value.rebase_declaration.value() == 0 ||
      value.trace_rebase_declaration.value() == 0 || value.provenance.value() == 0) {
    return false;
  }
  for (const auto& rule : value.rules) {
    if (rule.identity.value() == 0 || rule.lineage.value() == 0 ||
        rule.dependency_count == 0) { return false; }
  }
  return value.rules[0].identity != value.rules[1].identity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr theorem_expansion_receipt expand_theorem_fibers(
    const theorem_production_foundation& foundation,
    const theorem_production_goal& goal) noexcept {
  theorem_expansion_receipt receipt{};
  receipt.goal = goal;
  if (!valid_theorem_foundation(foundation)) { return receipt; }
  if (goal.identity.value() == 0 || goal.receiver.value() == 0 ||
      goal.target_type.value() == 0 || goal.metavariable.value() == 0) {
    receipt.obstruction = theorem_production_obstruction::missing_incidence;
    return receipt;
  }
  for (std::size_t slot = 0; slot < theorem_production_fiber_capacity; ++slot) {
    const auto& rule = foundation.rules[slot];
    receipt.fibers[slot] = {exact::word{goal.identity.value() + slot + 1U},
        rule.identity, rule.lineage, rule.formation, rule.dependency_count, true};
    ++receipt.open_count;
  }
  receipt.obstruction = theorem_production_obstruction::receiver_underdetermined;
  return receipt;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool restrict_theorem_fibers(
    theorem_expansion_receipt& expansion, theorem_proof_fiber& selected) noexcept {
  expansion.retained_count = 0;
  for (const auto& fiber : expansion.fibers) {
    if (fiber.open && fiber.dependency_count <= expansion.goal.maximum_dependencies) {
      selected = fiber;
      ++expansion.retained_count;
    }
  }
  return expansion.retained_count == 1;
}

}  // namespace holonics::organ
