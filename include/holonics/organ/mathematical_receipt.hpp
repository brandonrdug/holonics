#pragma once

#include <cstdint>

#include <holonics/organ/mathematical_schema.hpp>

namespace holonics::organ {

struct mathematical_neighborhood_receipt final {
  mathematical_goal question{};
  exact::word body_head{};
  exact::word environment{};
  exact::word source_material_testimony{};
  exact::word intersection_type{};
  exact::word proof_term{};
  exact::word proof_provenance{};
  exact::word declaration_ids[mathematical_neighborhood_capacity]{};
  exact::word dependency_lineages[mathematical_dependency_capacity]{};
  std::uint16_t declaration_count{};
  std::uint16_t dependency_count{};
  std::uint16_t dependency_joins{};
  std::uint16_t transport_alternatives{};
  std::uint16_t substitutions{};
  std::uint16_t unknown_count{};
  std::uint16_t global_declaration_scans{};
  mathematical_obstruction obstruction{mathematical_obstruction::invalid_foundation};
  bool term_match{};
  bool constraint_intersection{};
  bool proof_structurally_closed{};
  bool inherited_checked_example{};
  bool goal_open{};
  bool source_detached{};
  bool theorem_text_used_as_answer{};
  bool body_consumed{};
  bool body_cloned{};
};

}  // namespace holonics::organ
