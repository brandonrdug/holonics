#pragma once

#include <holonics/organ/theorem_production_schema.hpp>

namespace holonics::organ {

struct theorem_expansion_receipt final {
  theorem_production_goal goal{};
  theorem_proof_fiber fibers[theorem_production_fiber_capacity]{};
  std::uint16_t open_count{};
  std::uint16_t retained_count{};
  std::uint16_t global_candidate_scans{};
  theorem_production_obstruction obstruction{theorem_production_obstruction::invalid_foundation};
};

struct theorem_source_exclusion_receipt final {
  exact::word generated_statement{};
  exact::word generated_proof{};
  std::uint16_t mounted_answer_matches{};
  std::uint16_t lookup_entries{};
  std::uint16_t quoted_source_bytes{};
  std::uint16_t reference_calls{};
  std::uint32_t retained_development_source_bytes{};
  bool target_absent_at_mount{};
  bool source_detached_at_rest{};
};

struct theorem_probe_receipt final {
  dependent_theorem_goal goal{};
  exact::word body_head{};
  exact::word used_returned_fiber{};
  exact::word consequence{};
  theorem_production_obstruction obstruction{theorem_production_obstruction::returned_fiber_absent};
  std::uint16_t dependency_count{};
  std::uint16_t source_accesses{};
  bool available{};
};

struct theorem_ablation_receipt final {
  exact::word excluded_delta{};
  exact::word excluded_fiber{};
  theorem_probe_receipt production{};
  theorem_probe_receipt ablated{};
  bool exact_exclusion{};
  bool consequence_lost{};
};

struct theorem_generation_receipt final {
  theorem_expansion_receipt expansion{};
  theorem_passage passage{};
  theorem_source_exclusion_receipt exclusion{};
  theorem_production_obstruction obstruction{theorem_production_obstruction::invalid_foundation};
  bool exact_local_expansion{};
  bool exact_receiver_restriction{};
  bool proof_current_lineaged{};
};

}  // namespace holonics::organ
