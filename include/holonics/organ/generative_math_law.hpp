#pragma once

#include <cstddef>

#include <holonics/exact/integer_arithmetic.hpp>
#include <holonics/organ/generative_math_receipt.hpp>

namespace holonics::organ {

/// Exact carried addition. This helper outlived the conditioning organ it used to
/// live in; it is ordinary exact arithmetic and none of the removed mechanism.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool exact_add(
    std::uint64_t left, std::uint64_t right, std::uint64_t& result) noexcept {
  const auto value = exact::add(exact::unsigned_integer<1>::from_word(left),
      exact::unsigned_integer<1>::from_word(right));
  if (!value.accepted()) { return false; }
  result = value.value.limb(0);
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_generative_foundation(
    const generative_math_foundation& value) noexcept {
  if (value.ecology.value() == 0 || value.premise_declaration.value() == 0 ||
      value.premise_type.value() == 0 || value.premise_proof.value() == 0 ||
      value.provenance.value() == 0) {
    return false;
  }
  for (const auto& rule : value.rules) {
    if (rule.identity.value() == 0 || rule.port.value() == 0 ||
        rule.lineage.value() == 0 || rule.dependency_count == 0) {
      return false;
    }
  }
  return value.rules[0].identity != value.rules[1].identity;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr generative_expansion_receipt
expand_generative_fibers(
    const generative_math_foundation& foundation,
    const generative_math_goal& goal) noexcept {
  generative_expansion_receipt receipt{};
  receipt.goal = goal;
  if (!valid_generative_foundation(foundation)) { return receipt; }
  if (goal.identity.value() == 0 || goal.receiver.value() == 0 ||
      goal.metavariable.value() == 0 || !goal.reverse_orientation ||
      goal.premise_declaration != foundation.premise_declaration ||
      goal.target_type != foundation.premise_type) {
    receipt.obstruction = generative_obstruction::missing_incidence;
    return receipt;
  }
  for (std::size_t slot = 0; slot < generative_fiber_capacity; ++slot) {
    const auto& rule = foundation.rules[slot];
    std::uint64_t fiber_identity = 0;
    if (!exact_add(goal.identity.value(), slot + 1U, fiber_identity)) {
      receipt.obstruction = generative_obstruction::arithmetic_refused;
      return receipt;
    }
    receipt.fibers[slot] = {exact::word{fiber_identity}, rule.identity,
        rule.lineage, rule.formation, rule.dependency_count, true};
    ++receipt.open_count;
  }
  receipt.obstruction = generative_obstruction::receiver_underdetermined;
  return receipt;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool restrict_generative_fibers(
    const generative_expansion_receipt& expansion,
    proof_fiber& selected,
    std::uint16_t& retained) noexcept {
  retained = 0;
  for (const auto& fiber : expansion.fibers) {
    if (fiber.open && fiber.dependency_count <= expansion.goal.maximum_dependencies) {
      selected = fiber;
      ++retained;
    }
  }
  return retained == 1;
}

}  // namespace holonics::organ
