#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/mathematical_receipt.hpp>

namespace holonics::organ {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool valid_mathematical_foundation(
    const mathematical_foundation& value) noexcept {
  if (value.environment.value() == 0 || value.kernel_declarations.value() == 0 ||
      value.provenance.value() == 0 || value.source_material_testimony.value() == 0 ||
      value.term_count == 0 || value.term_count > mathematical_term_capacity ||
      value.declaration_count == 0 ||
      value.declaration_count > mathematical_declaration_capacity ||
      value.dependency_count > mathematical_dependency_capacity) {
    return false;
  }
  for (std::size_t slot = 0; slot < value.term_count; ++slot) {
    const auto& term = value.terms[slot];
    if (term.identity.value() == 0 || term.type_identity.value() == 0 ||
        term.provenance.value() == 0 ||
        (term.has_left && term.left_slot >= value.term_count) ||
        (term.has_right && term.right_slot >= value.term_count)) {
      return false;
    }
  }
  for (std::size_t slot = 0; slot < value.declaration_count; ++slot) {
    const auto& declaration = value.declarations[slot];
    const std::size_t dependency_end =
        static_cast<std::size_t>(declaration.dependency_begin) + declaration.dependency_count;
    if (declaration.identity.value() == 0 || declaration.provenance.value() == 0 ||
        declaration.type_slot >= value.term_count ||
        (declaration.has_value && declaration.value_slot >= value.term_count) ||
        dependency_end > value.dependency_count) {
      return false;
    }
  }
  for (std::size_t slot = 0; slot < value.dependency_count; ++slot) {
    const auto& dependency = value.dependencies[slot];
    if (dependency.target_slot >= value.declaration_count || dependency.port.value() == 0 ||
        dependency.lineage.value() == 0) {
      return false;
    }
  }
  return true;
}

HOLONICS_CALLABLE constexpr bool add_declaration_identity(
    mathematical_neighborhood_receipt& receipt, exact::word identity) noexcept {
  if (receipt.declaration_count == mathematical_neighborhood_capacity) { return false; }
  std::size_t insert = receipt.declaration_count;
  while (insert != 0 && receipt.declaration_ids[insert - 1].value() > identity.value()) {
    receipt.declaration_ids[insert] = receipt.declaration_ids[insert - 1];
    --insert;
  }
  receipt.declaration_ids[insert] = identity;
  ++receipt.declaration_count;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool inherited_proof_is_closed(
    const mathematical_foundation& foundation,
    const mathematical_declaration& declaration) noexcept {
  if (!declaration.has_value || !declaration.inherited_checked_example) { return false; }
  const auto& type = foundation.terms[declaration.type_slot];
  const auto& proof = foundation.terms[declaration.value_slot];
  if (proof.constructor != term_constructor::proof ||
      proof.type_identity != type.identity || proof.provenance != declaration.provenance) {
    return false;
  }
  if (proof.has_left && proof.left_slot >= foundation.term_count) { return false; }
  if (proof.has_right && proof.right_slot >= foundation.term_count) { return false; }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr mathematical_neighborhood_receipt
reconstruct_mathematical_neighborhood(
    const mathematical_foundation& foundation,
    exact::word body_head,
    const mathematical_goal& question,
    bool source_detached) noexcept {
  mathematical_neighborhood_receipt receipt{};
  receipt.question = question;
  receipt.body_head = body_head;
  receipt.environment = foundation.environment;
  receipt.source_material_testimony = foundation.source_material_testimony;
  receipt.source_detached = source_detached;
  if (!valid_mathematical_foundation(foundation)) { return receipt; }
  if (question.identity.value() == 0 || question.receiver.value() == 0 ||
      question.metavariable.value() == 0 || question.anchor_slot >= foundation.declaration_count) {
    receipt.obstruction = mathematical_obstruction::missing_incidence;
    return receipt;
  }
  const auto& anchor = foundation.declarations[question.anchor_slot];
  const auto& anchor_type = foundation.terms[anchor.type_slot];
  receipt.term_match = anchor_type.identity == question.target_type;
  receipt.intersection_type = receipt.term_match ? anchor_type.identity : exact::word{};
  receipt.constraint_intersection = receipt.term_match;
  receipt.unknown_count = 1;
  receipt.goal_open = true;
  if (!receipt.term_match) {
    receipt.obstruction = mathematical_obstruction::type_mismatch;
    return receipt;
  }

  bool visited[mathematical_declaration_capacity]{};
  std::uint16_t frontier[mathematical_declaration_capacity]{};
  std::size_t read = 0;
  std::size_t write = 1;
  frontier[0] = question.anchor_slot;
  visited[question.anchor_slot] = true;
  while (read < write) {
    const std::uint16_t declaration_slot = frontier[read++];
    const auto& declaration = foundation.declarations[declaration_slot];
    if (!add_declaration_identity(receipt, declaration.identity)) {
      receipt.obstruction = mathematical_obstruction::capacity_refused;
      return receipt;
    }
    for (std::size_t offset = 0; offset < declaration.dependency_count; ++offset) {
      const auto& dependency =
          foundation.dependencies[declaration.dependency_begin + offset];
      if (receipt.dependency_count == mathematical_dependency_capacity) {
        receipt.obstruction = mathematical_obstruction::capacity_refused;
        return receipt;
      }
      receipt.dependency_lineages[receipt.dependency_count++] = dependency.lineage;
      ++receipt.dependency_joins;
      if (dependency.role == dependency_role::lemma_transport) {
        ++receipt.transport_alternatives;
      }
      if (!visited[dependency.target_slot]) {
        if (write == mathematical_declaration_capacity) {
          receipt.obstruction = mathematical_obstruction::capacity_refused;
          return receipt;
        }
        visited[dependency.target_slot] = true;
        frontier[write++] = dependency.target_slot;
      }
    }
  }
  if (question.hypothesis_type == anchor_type.identity) { receipt.substitutions = 1; }
  receipt.proof_structurally_closed = inherited_proof_is_closed(foundation, anchor);
  receipt.inherited_checked_example = anchor.inherited_checked_example;
  if (anchor.has_value) {
    receipt.proof_term = foundation.terms[anchor.value_slot].identity;
    receipt.proof_provenance = foundation.terms[anchor.value_slot].provenance;
  }
  receipt.obstruction = question.request_generated_closure
      ? mathematical_obstruction::unsolved_goal : mathematical_obstruction::none;
  return receipt;
}

}  // namespace holonics::organ
