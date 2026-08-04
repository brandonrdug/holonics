#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/conditioning_schema.hpp>

namespace holonics::organ {

inline constexpr std::size_t generative_fiber_capacity = 2;

enum class proof_formation : std::uint8_t { equivalence_symmetry, paired_implications };
enum class generative_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  missing_incidence,
  receiver_underdetermined,
  no_consequence,
  continuation_refused,
  render_refused,
  arithmetic_refused
};

struct generative_local_rule final {
  exact::word identity{};
  exact::word port{};
  exact::word lineage{};
  proof_formation formation{proof_formation::equivalence_symmetry};
  std::uint16_t dependency_count{};
};

struct generative_math_foundation final {
  exact::word ecology{};
  exact::word premise_declaration{};
  exact::word premise_type{};
  exact::word premise_proof{};
  exact::word provenance{};
  navigation_morphology conditioning{};
  generative_local_rule rules[generative_fiber_capacity]{};
};

struct generative_math_goal final {
  exact::word identity{};
  exact::word receiver{};
  exact::word premise_declaration{};
  exact::word target_type{};
  exact::word metavariable{};
  std::uint16_t maximum_dependencies{};
  bool reverse_orientation{};
};

struct proof_fiber final {
  exact::word identity{};
  exact::word rule{};
  exact::word lineage{};
  proof_formation formation{proof_formation::equivalence_symmetry};
  std::uint16_t dependency_count{};
  bool open{};
};

struct generated_math_passage final {
  exact::word identity{};
  exact::word statement{};
  exact::word proof{};
  exact::word target_type{};
  exact::word premise_declaration{};
  exact::word selected_rule{};
  exact::word lineage{};
  proof_formation formation{proof_formation::equivalence_symmetry};
  bool closed{};
  bool generated{};
};

}  // namespace holonics::organ
