#pragma once

#include <cstdint>

#include <holonics/organ/conditioning_receipt.hpp>
#include <holonics/organ/generative_math_schema.hpp>

namespace holonics::organ {

struct generative_expansion_receipt final {
  generative_math_goal goal{};
  proof_fiber fibers[generative_fiber_capacity]{};
  std::uint16_t open_count{};
  std::uint16_t global_candidate_scans{};
  generative_obstruction obstruction{generative_obstruction::invalid_foundation};
};

struct generated_source_exclusion final {
  exact::word generated_statement{};
  exact::word generated_proof{};
  std::uint16_t mounted_answer_matches{};
  std::uint16_t lookup_entries{};
  std::uint16_t quoted_source_bytes{};
  bool distinct_from_inherited{};
  bool absent_before_generation{};
};

struct causal_information_receipt final {
  exact::word question{};
  exact::word receiver{};
  exact::word predecessor{};
  exact::word successor{};
  exact::word continuation{};
  exact::word selected_lineage{};
  exact::word morphology_delta{};
  std::uint16_t alternatives_before{};
  std::uint16_t alternatives_after{};
  generative_obstruction returned_obstruction{generative_obstruction::invalid_foundation};
  bool obstruction_changed_passage{};
  bool receiver_indexed{};
  bool committed{};
};

struct generative_math_receipt final {
  generative_expansion_receipt expansion{};
  navigation_consequence conditioning{};
  generated_math_passage passage{};
  generated_source_exclusion exclusion{};
  causal_information_receipt information{};
  generative_obstruction obstruction{generative_obstruction::invalid_foundation};
  bool exact_local_expansion{};
  bool exact_receiver_restriction{};
  bool proof_current_lineaged{};
  bool score_used{};
  bool registry_used{};
};

}  // namespace holonics::organ
