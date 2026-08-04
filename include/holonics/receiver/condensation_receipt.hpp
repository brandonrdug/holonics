#pragma once

#include <cstdint>

#include <holonics/receiver/condensation_schema.hpp>

namespace holonics::receiver {

enum class condensation_obstruction : std::uint8_t {
  none,
  invalid_program,
  family_mismatch,
  unfactorable_query,
  arithmetic_refused,
  continuation_refused
};

struct condensed_snapshot final {
  exact::word head{};
  exact::word incidence{};
  exact::word morphology{};
  exact::word current{};
  exact::word lineage{};
  exact::word logical_resource{};
  exact::word alternatives{};
  exact::word source_identities[condensation_source_capacity]{};
  exact::word source_values[condensation_source_capacity]{};
  condensation_obstruction obstruction{condensation_obstruction::none};
  std::uint16_t source_count{};
};

struct factorized_boundary_response final {
  exact::word family{};
  exact::word version{};
  exact::word query{};
  exact::word direct{};
  exact::word factorized{};
  exact::word retained_source_support{};
  std::uint16_t factor_count{};
  bool exact{};
};

struct boundary_bisimulation_step final {
  exact::word input_occurrence{};
  exact::word input_port{};
  exact::word common_predecessor{};
  exact::word direct_input_language{};
  exact::word condensed_input_language{};
  factorized_boundary_response response{};
  condensed_snapshot direct_successor{};
  condensed_snapshot condensed_successor{};
  condensation_obstruction direct_obstruction{condensation_obstruction::none};
  condensation_obstruction condensed_obstruction{condensation_obstruction::none};
  bool next_language_equal{};
  bool testimony_equal{};
  bool obstruction_equal{};
  bool incidence_equal{};
  bool current_equal{};
  bool morphology_equal{};
  bool alternatives_equal{};
  bool lineage_equal{};
  bool logical_resource_equal{};
  bool complete_successor_equal{};
};

struct boundary_refinement_receipt final {
  exact::word occurrence{};
  exact::word predecessor{};
  exact::word successor{};
  exact::word old_family{};
  exact::word old_version{};
  exact::word new_family{};
  exact::word new_version{};
  exact::word reconstruction_capability{};
  exact::word lineage{};
  std::uint16_t old_group_count{};
  std::uint16_t new_group_count{};
  bool family_grew{};
  bool source_reopened{};
  bool exact_reconstruction{};
  bool retained_fiber{};
};

struct condensation_observation final {
  exact::word program_identity{};
  condensed_snapshot predecessor{};
  condensed_snapshot successor{};
  boundary_bisimulation_step history[condensation_history_capacity]{};
  boundary_refinement_receipt refinement{};
  condensation_obstruction obstruction{condensation_obstruction::none};
  std::uint16_t history_count{};
  bool factorized_boundary{};
  bool stateful_bisimulation{};
  bool source_fiber_retained{};
  bool non_resumable{};
};

}  // namespace holonics::receiver
