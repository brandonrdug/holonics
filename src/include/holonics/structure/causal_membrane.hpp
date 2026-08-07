#pragma once

#include <concepts>
#include <cstdint>

#include <holonics/structure/branch_lineage.hpp>
#include <holonics/structure/transition_invariants.hpp>

namespace holonics::structure {

struct membrane_marker final {};

/// The single atomic receiving contract.
///
/// One membrane owns one standing and receives one occurrence at a time,
/// returning either a typed return or a typed refusal. There is no second mouth,
/// no batch entry point that bypasses the invariants, and no path that mutates
/// standing without producing a return.
template<class Membrane>
concept causal_membrane = requires(
    Membrane& body,
    const Membrane& observed,
    typename Membrane::occurrence_type occurrence) {
  typename Membrane::holonics_membrane;
  typename Membrane::standing_type;
  typename Membrane::occurrence_type;
  typename Membrane::return_type;
  typename Membrane::refusal_type;
  { observed.standing() } -> std::same_as<const typename Membrane::standing_type&>;
  { body.receive_occurrence(occurrence) };
} && std::same_as<typename Membrane::holonics_membrane, membrane_marker>;

/// What a membrane returns: the successor's identity, the transition grade, and
/// the disposition the passage reached. A refusal returns the body intact.
template<class Return>
struct membrane_crossing final {
  Return value{};
  transition_grade grade{};
  returned_disposition disposition{};
  exact::word predecessor{};
  exact::word successor{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool committed() const noexcept {
    return grade.complete() && successor.value() != 0;
  }
};

/// A staged crossing that has not yet committed. `into_parts` hands back BOTH
/// the untouched body identity and the staged occurrence, so a refusal never
/// destroys either.
template<class Occurrence>
struct staged_crossing final {
  Occurrence occurrence{};
  exact::word predecessor{};
  transition_grade grade{};
  bool admitted{};
};

namespace membrane_law {

/// A staged crossing may commit only against the predecessor it was staged on.
/// A device return that arrives against a different predecessor is refused, not
/// rebased.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool may_commit(
    exact::word staged_predecessor,
    exact::word current_predecessor) noexcept {
  return staged_predecessor.value() != 0 &&
      staged_predecessor == current_predecessor;
}

/// Neither a count, a key order, a worker lane, nor a host loop position
/// establishes causality or commutation. This predicate exists to be called at
/// every place a caller might be tempted to infer one, and it always refuses.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool apparatus_establishes_causality(
    std::uint64_t /*worker_lane*/,
    std::uint64_t /*completion_order*/,
    std::uint64_t /*serialized_position*/) noexcept {
  return false;
}

/// Parallel admission requires a typed complete-successor equality receipt over
/// morphology, return, obstruction, resource state, and lineage. Anything short
/// of all five leaves the crossing ordered or open.
struct interchange_receipt final {
  bool successor_equal{};
  bool return_equal{};
  bool obstruction_equal{};
  bool resource_state_equal{};
  bool lineage_equal{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool commutes() const noexcept {
    return successor_equal && return_equal && obstruction_equal &&
        resource_state_equal && lineage_equal;
  }
};

}  // namespace membrane_law
}  // namespace holonics::structure
