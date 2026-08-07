#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {
inline constexpr std::size_t theorem_production_fiber_capacity = 2;

enum class theorem_formation : std::uint8_t {
  compose_then_transport,
  transport_then_compose,
  returned_fiber_extension
};

enum class theorem_production_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  missing_incidence,
  receiver_underdetermined,
  no_consequence,
  continuation_refused,
  render_refused,
  pending_return,
  checker_rejected,
  rest_refused,
  returned_fiber_absent
};

struct theorem_local_rule final {
  exact::word identity{};
  exact::word lineage{};
  theorem_formation formation{theorem_formation::compose_then_transport};
  std::uint16_t dependency_count{};
};

struct theorem_production_foundation final {
  exact::word ecology{};
  exact::word trace_declaration{};
  exact::word trace_trans_declaration{};
  exact::word rebase_declaration{};
  exact::word trace_rebase_declaration{};
  exact::word provenance{};
  theorem_local_rule rules[theorem_production_fiber_capacity]{};
};

struct theorem_production_goal final {
  exact::word identity{};
  exact::word receiver{};
  exact::word target_type{};
  exact::word metavariable{};
  std::uint16_t maximum_dependencies{};
};

struct dependent_theorem_goal final {
  exact::word identity{};
  exact::word receiver{};
  exact::word required_returned_fiber{};
  exact::word target_type{};
  std::uint16_t maximum_dependencies{};
};

struct theorem_proof_fiber final {
  exact::word identity{};
  exact::word rule{};
  exact::word lineage{};
  theorem_formation formation{theorem_formation::compose_then_transport};
  std::uint16_t dependency_count{};
  bool open{};
};

struct theorem_passage final {
  exact::word identity{};
  exact::word statement{};
  exact::word proof{};
  exact::word target_type{};
  exact::word selected_rule{};
  exact::word lineage{};
  theorem_formation formation{theorem_formation::compose_then_transport};
  bool closed{};
  bool generated{};
};

struct acquired_theorem_fiber final {
  exact::word identity{};
  exact::word passage{};
  exact::word statement{};
  exact::word proof{};
  exact::word kernel_return{};
  exact::word selected_rule{};
  std::uint16_t dependency_count{};
  bool accepted{};
};

}  // namespace holonics::organ
