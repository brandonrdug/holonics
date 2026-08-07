#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/directed_dependency.hpp>
#include <holonics/structure/disposition.hpp>

namespace holonics::structure {

/// The eight invariants of one atomic successor
///
/// ```text
///     Lambda : (S_t, L_e)  ->  (S_t+, R_e)
/// ```
///
/// Testimony is a projection of the transition, never an input to it.
enum class transition_invariant : std::uint8_t {
  same_prestate_atomicity = 0,
  no_false_incidence = 1,
  occurrence_preservation = 2,
  oriented_boundary_validity = 3,
  causal_attribution = 4,
  one_visibility_edge = 5,
  rest_performs_no_event = 6,
  bounded_emission = 7
};

inline constexpr std::uint8_t transition_invariant_count = 8;

/// The provenance an occurrence carries through a transition. These four remain
/// distinguishable at every boundary where the distinction matters; collapsing
/// them is the causal-attribution failure.
enum class causal_attribution : std::uint8_t {
  inherited,
  contacted,
  returned,
  self_emanated
};

struct transition_grade final {
  std::uint8_t satisfied{};
  std::uint8_t refused_at{transition_invariant_count};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool complete() const noexcept {
    return satisfied == static_cast<std::uint8_t>((1U << transition_invariant_count) - 1U) &&
        refused_at == transition_invariant_count;
  }
};

namespace transition_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t bit(
    transition_invariant invariant) noexcept {
  return static_cast<std::uint8_t>(1U << static_cast<std::uint8_t>(invariant));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool holds(
    transition_grade grade,
    transition_invariant invariant) noexcept {
  return (grade.satisfied & bit(invariant)) != 0U;
}

/// Record one invariant as satisfied. The first refusal is retained; later
/// invariants are still recorded so the receipt names everything that held.
[[nodiscard]] HOLONICS_CALLABLE constexpr transition_grade admit(
    transition_grade grade,
    transition_invariant invariant,
    bool satisfied) noexcept {
  if (satisfied) {
    grade.satisfied = static_cast<std::uint8_t>(grade.satisfied | bit(invariant));
    return grade;
  }
  if (grade.refused_at == transition_invariant_count) {
    grade.refused_at = static_cast<std::uint8_t>(invariant);
  }
  return grade;
}

/// Same-prestate atomicity: every interacting member of the incoming population
/// meets the SAME predecessor standing.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_prestate(
    exact::word declared_predecessor,
    const exact::word* met_predecessors,
    std::uint16_t count) noexcept {
  if (declared_predecessor.value() == 0 || count == 0) {
    return false;
  }
  for (std::uint16_t slot = 0; slot < count; ++slot) {
    if (met_predecessors[slot] != declared_predecessor) {
      return false;
    }
  }
  return true;
}

/// No false incidence: only source-declared incidence, or incidence formed by an
/// admitted rewrite or junction law, enters the successor.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool no_false_incidence(
    const oriented_boundary<Capacity>& successor,
    const oriented_boundary<Capacity>& declared) noexcept {
  for (std::uint16_t index = 0; index < successor.used; ++index) {
    bool found = false;
    for (std::uint16_t other = 0; other < declared.used; ++other) {
      const oriented_incidence& left = successor.faces[index];
      const oriented_incidence& right = declared.faces[other];
      if (left.cell == right.cell && left.face == right.face &&
          left.sign == right.sign && left.slot == right.slot) {
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

/// Occurrence preservation: equal disconnected occurrences remain plural.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool occurrences_preserved(
    std::uint32_t before,
    std::uint32_t caused,
    std::uint32_t after) noexcept {
  return after == before + caused;
}

/// Rest performs no event: a remount or a wait without new current advances
/// nothing.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool rest_is_eventless(
    exact::word head_before,
    exact::word head_after,
    bool current_supplied) noexcept {
  return current_supplied || head_before == head_after;
}

/// Bounded emission: the successor carries consequential relation and exposed
/// residual, not an obligatory crystal history of the event interior.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool emission_bounded(
    std::uint32_t emitted,
    std::uint32_t interior_visited) noexcept {
  return emitted <= interior_visited;
}

/// Oriented boundary validity: the two transports of a Chi are a genuine
/// **parallel pair** — same source, same target, distinct identities. A pair
/// that does not share both endpoints is not two routes between the same two
/// places, and the residual between them measures nothing.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool boundary_parallel(
    const local_transport& composed,
    const local_transport& direct) noexcept {
  return transport_law::admitted(composed) && transport_law::admitted(direct) &&
      composed.source == direct.source && composed.target == direct.target &&
      composed.identity != direct.identity;
}

/// Causal attribution: the four provenances stay distinguishable, and the
/// disposition must match how the difference arrived.
///
/// **A FOUND may only issue from material that arrived** — contacted, or the
/// body's own emanation returning. **A RIDE may only issue from what already
/// stands** — inherited terrain, or a prior return. That is the Swing's
/// asymmetry read as an attribution law: founding pays curvature and therefore
/// needs something new; riding is cheap because the terrain already paid.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool attribution_matches(
    causal_attribution attribution,
    bool founded,
    bool concluded) noexcept {
  if (!concluded) {
    return true;
  }
  const bool arrived = attribution == causal_attribution::contacted ||
      attribution == causal_attribution::self_emanated;
  return founded == arrived;
}

/// One visibility edge: a crossing exposes exactly one edge to the world. Not
/// zero — that is a crossing that changed nothing while claiming to conclude —
/// and not several, which would make the successor's visibility ambiguous.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool single_visibility_edge(
    std::uint32_t placements,
    std::uint32_t advanced_lineages) noexcept {
  return placements == 1U && advanced_lineages == 1U;
}

}  // namespace transition_law
}  // namespace holonics::structure
