#pragma once

#include <cstddef>

#include <holonics/event/dependent_theorem_setup.hpp>
#include <holonics/organ/theorem_production_law.hpp>

namespace holonics::event {

struct dependent_theorem_generation_receipt final {
  organ::dependent_theorem_goal goal{};
  organ::theorem_proof_fiber fibers[organ::theorem_production_fiber_capacity]{};
  organ::theorem_proof_fiber selected{};
  organ::theorem_passage passage{};
  organ::theorem_source_exclusion_receipt exclusion{};
  exact::word inherited_passage{};
  exact::word inherited_kernel_return{};
  exact::word inherited_returned_fiber{};
  exact::word selected_witness{};
  std::uint16_t open_count{};
  std::uint16_t retained_count{};
  std::uint16_t global_candidate_scans{};
  organ::theorem_production_obstruction alternative_obstruction{
      organ::theorem_production_obstruction::receiver_underdetermined};
  organ::theorem_production_obstruction obstruction{
      organ::theorem_production_obstruction::missing_incidence};
  bool exact_local_expansion{};
  bool exact_receiver_restriction{};
  bool dependency_exact{};
  bool proof_current_lineaged{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool form_dependent_theorem(
    const organ::theorem_production_foundation& foundation,
    const organ::acquired_theorem_fiber& inherited,
    const dependent_theorem_setup& setup,
    dependent_theorem_generation_receipt& receipt) noexcept {
  receipt.alternative_obstruction =
      organ::theorem_production_obstruction::receiver_underdetermined;
  receipt.obstruction = organ::theorem_production_obstruction::missing_incidence;
  receipt.goal = {setup.question.identity, setup.question.receiver,
      setup.question.required_returned_fiber, setup.question.target_type,
      setup.question.maximum_dependencies};
  if (!organ::valid_theorem_foundation(foundation) || !setup.frozen ||
      !setup.complete_source_absent || !setup.factors_through_returned_fiber ||
      setup.integrity != dependent_setup_integrity(setup) ||
      setup.statement.value() == 0 || setup.proof.value() == 0 ||
      setup.passage.value() == 0 || setup.selected_route.value() == 0) {
    return false;
  }
  if (!inherited.accepted || inherited.identity != setup.question.required_returned_fiber) {
    receipt.obstruction = organ::theorem_production_obstruction::returned_fiber_absent;
    return false;
  }
  receipt.fibers[0] = {setup.selected_route, inherited.identity,
      inherited.kernel_return, organ::theorem_formation::returned_fiber_extension,
      setup.dependency_count, true};
  receipt.fibers[1] = {exact::word{setup.selected_route.value() + 1U},
      foundation.rules[1].identity, foundation.rules[1].lineage,
      organ::theorem_formation::transport_then_compose,
      foundation.rules[1].dependency_count, true};
  receipt.open_count = 2;
  for (const auto& fiber : receipt.fibers) {
    if (fiber.open && fiber.dependency_count <= setup.question.maximum_dependencies) {
      receipt.selected = fiber;
      ++receipt.retained_count;
    }
  }
  if (receipt.retained_count != 1 || receipt.selected.identity != setup.selected_route) {
    receipt.obstruction = organ::theorem_production_obstruction::no_consequence;
    return false;
  }
  receipt.passage = {setup.passage, setup.statement, setup.proof,
      setup.question.target_type, inherited.identity, inherited.identity,
      organ::theorem_formation::returned_fiber_extension, true, true};
  receipt.exclusion.generated_statement = setup.statement;
  receipt.exclusion.generated_proof = setup.proof;
  receipt.exclusion.target_absent_at_mount = setup.complete_source_absent;
  receipt.inherited_passage = inherited.passage;
  receipt.inherited_kernel_return = inherited.kernel_return;
  receipt.inherited_returned_fiber = inherited.identity;
  receipt.selected_witness = receipt.selected.identity;
  receipt.exact_local_expansion = true;
  receipt.exact_receiver_restriction = true;
  receipt.dependency_exact = receipt.passage.selected_rule == inherited.identity &&
      receipt.inherited_returned_fiber == setup.question.required_returned_fiber;
  receipt.proof_current_lineaged = true;
  receipt.obstruction = organ::theorem_production_obstruction::none;
  return true;
}

}  // namespace holonics::event
