#pragma once

#include <cstdint>

#include <holonics/organ/suffix_symbol.hpp>
#include <holonics/structure/resident_span.hpp>

namespace holonics::organ {

/// One automaton state.
///
/// `material_end_multiplicity` counts how many distinct causal testimonies ended
/// here. **Duplicate testimony is recurrence, not redundancy**: repeated
/// passages are retained as multiplicity and are never deduplicated, and the
/// count is never normalized into a probability.
///
/// `first_transition` heads this state's **own** fan-out chain, held in the
/// canonical symbol order. A lookup touches one state's outgoing symbols and
/// never the transition population of the body — the source owner holds
/// transitions per state for exactly this reason (`suffix_ecology.rs:85`).
///
/// `last_transition` is that chain's tail. Separators are necessarily one per
/// informant path and sort after all germ material, so the root receives a
/// strictly ascending run of them; without the tail every separator would walk
/// the whole germ population and every earlier separator, and root insertion
/// would be quadratic in the source count.
struct suffix_state final {
  std::uint32_t maximum_length{};
  std::uint32_t link{no_state};
  std::uint64_t material_end_multiplicity{};
  std::uint32_t first_transition{no_transition};
  std::uint32_t last_transition{no_transition};
};

struct suffix_transition final {
  std::uint32_t from{};
  std::uint32_t to{};
  suffix_symbol symbol{};
};

/// The exact suffix ecology, held in resident storage it does not own.
///
/// A generalized suffix automaton founding **at most two states per symbol** —
/// the new end state and at most one clone — so the population stays inside the
/// exact `2N` bound rather than enumerating an n-gram powerset. It emits **no
/// root vocabulary** and holds no scores: a continuation is exposed with its
/// source state, matched length, target state, and multiplicity, and nothing
/// here selects among them.
///
/// The arena is spans plus counters, so **the whole ecology crosses to a kernel
/// as pointers**. `lookup_steps` is apparatus testimony over fan-out work; it
/// enters no admission, no ordering, and no return.
struct suffix_arena final {
  structure::resident_span<suffix_state> states{};
  structure::resident_span<suffix_transition> transitions{};
  structure::resident_span<std::uint32_t> next{};
  std::uint32_t states_used{};
  std::uint32_t transitions_used{};
  std::uint32_t last{};
  std::uint64_t lookup_steps{};
};

namespace suffix_law {

/// Found the root. An arena without storage refuses rather than writing.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_found_root(
    suffix_arena& arena) noexcept {
  if (!arena.states.holds(0) || !arena.transitions.present() ||
      arena.next.extent != arena.transitions.extent) {
    return false;
  }
  arena.states.at(0) = suffix_state{0, no_state, 0, no_transition};
  arena.states_used = 1;
  arena.transitions_used = 0;
  arena.last = 0;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr const suffix_state* state_at(
    const suffix_arena& arena,
    std::uint32_t state) noexcept {
  return state < arena.states_used ? &arena.states.at(state) : nullptr;
}

/// Follow one symbol out of one state. The chain is sorted, so the walk stops at
/// the first symbol that follows the one sought.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t transition(
    suffix_arena& arena,
    std::uint32_t from,
    suffix_symbol symbol) noexcept {
  if (from >= arena.states_used) {
    return no_state;
  }
  for (std::uint32_t slot = arena.states.at(from).first_transition;
       slot != no_transition; slot = arena.next.at(slot)) {
    arena.lookup_steps = arena.lookup_steps + 1U;
    if (equal(arena.transitions.at(slot).symbol, symbol)) {
      return arena.transitions.at(slot).to;
    }
    if (precedes(symbol, arena.transitions.at(slot).symbol)) {
      return no_state;
    }
  }
  return no_state;
}

/// The reading form of `transition`.
///
/// **The arena is const, so a query path cannot found, link, retarget, or
/// clone — that is a type error here, not a runtime check.** This is what a
/// resident device query uses: the card reads the host's standing and can only
/// read it.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t transition_read(
    const suffix_arena& arena,
    std::uint32_t from,
    suffix_symbol symbol) noexcept {
  if (from >= arena.states_used) {
    return no_state;
  }
  for (std::uint32_t slot = arena.states.at(from).first_transition;
       slot != no_transition; slot = arena.next.at(slot)) {
    if (equal(arena.transitions.at(slot).symbol, symbol)) {
      return arena.transitions.at(slot).to;
    }
    if (precedes(symbol, arena.transitions.at(slot).symbol)) {
      return no_state;
    }
  }
  return no_state;
}

/// The reading form of `follow`. Same const guarantee.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t follow_read(
    const suffix_arena& arena,
    const suffix_symbol* path,
    std::uint32_t count,
    std::uint32_t& matched) noexcept {
  std::uint32_t state = 0;
  matched = 0;
  for (std::uint32_t slot = 0; slot < count; ++slot) {
    const std::uint32_t next = transition_read(arena, state, path[slot]);
    if (next == no_state) {
      return state;
    }
    state = next;
    matched = matched + 1U;
  }
  return state;
}

/// Return to the root. A boundary between informant paths resets the active
/// state so a later path cannot continue an earlier one by material alone.
HOLONICS_CALLABLE constexpr void separate(suffix_arena& arena) noexcept {
  arena.last = 0;
}

/// Follow a path from the root. Returns the state reached and the matched
/// length; an unmatched symbol returns the root with length zero rather than
/// fabricating a continuation.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t follow(
    suffix_arena& arena,
    const suffix_symbol* path,
    std::uint32_t count,
    std::uint32_t& matched) noexcept {
  std::uint32_t state = 0;
  matched = 0;
  for (std::uint32_t slot = 0; slot < count; ++slot) {
    const std::uint32_t next = transition(arena, state, path[slot]);
    if (next == no_state) {
      return state;
    }
    state = next;
    matched = matched + 1U;
  }
  return state;
}

/// Every locally supported continuation of a state, in canonical symbol order.
/// **No score, no ranking, no selected answer** — the caller receives the whole
/// population, read off this state's own chain.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t continuations(
    const suffix_arena& arena,
    std::uint32_t from,
    suffix_transition* out,
    std::uint32_t limit) noexcept {
  std::uint32_t found = 0;
  if (from >= arena.states_used) {
    return found;
  }
  for (std::uint32_t slot = arena.states.at(from).first_transition;
       slot != no_transition && found < limit; slot = arena.next.at(slot)) {
    out[found] = arena.transitions.at(slot);
    found = found + 1U;
  }
  return found;
}

}  // namespace suffix_law

}  // namespace holonics::organ
