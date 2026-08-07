#pragma once

#include <cstdint>

#include <holonics/organ/suffix_arena.hpp>

namespace holonics::organ::suffix_law {

/// Splice one transition into `from`'s own chain in canonical symbol order. The
/// chain stays sorted, so a lookup stops at the first symbol that follows the
/// one sought and `continuations` exposes a canonical order rather than a
/// reverse-insertion accident.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_link(
    suffix_arena& arena,
    std::uint32_t from,
    suffix_symbol symbol,
    std::uint32_t to) noexcept {
  if (!arena.transitions.holds(arena.transitions_used)) {
    return false;
  }
  const std::uint32_t minted = arena.transitions_used;
  arena.transitions.at(minted) = suffix_transition{from, to, symbol};
  arena.transitions_used = arena.transitions_used + 1U;
  const std::uint32_t tail = arena.states.at(from).last_transition;
  // The ascending case, which is the separator population at the root and every
  // clone copy: constant work, no walk.
  if (tail != no_transition && precedes(arena.transitions.at(tail).symbol, symbol)) {
    arena.next.at(tail) = minted;
    arena.next.at(minted) = no_transition;
    arena.states.at(from).last_transition = minted;
    return true;
  }
  std::uint32_t before = no_transition;
  std::uint32_t walk = arena.states.at(from).first_transition;
  while (walk != no_transition && precedes(arena.transitions.at(walk).symbol, symbol)) {
    arena.lookup_steps = arena.lookup_steps + 1U;
    before = walk;
    walk = arena.next.at(walk);
  }
  arena.next.at(minted) = walk;
  if (before == no_transition) {
    arena.states.at(from).first_transition = minted;
  } else {
    arena.next.at(before) = minted;
  }
  if (walk == no_transition) {
    arena.states.at(from).last_transition = minted;
  }
  return true;
}

HOLONICS_CALLABLE constexpr void retarget(
    suffix_arena& arena,
    std::uint32_t from,
    suffix_symbol symbol,
    std::uint32_t to) noexcept {
  for (std::uint32_t slot = arena.states.at(from).first_transition;
       slot != no_transition; slot = arena.next.at(slot)) {
    arena.lookup_steps = arena.lookup_steps + 1U;
    if (equal(arena.transitions.at(slot).symbol, symbol)) {
      arena.transitions.at(slot).to = to;
      return;
    }
    if (precedes(symbol, arena.transitions.at(slot).symbol)) {
      return;
    }
  }
}

/// Copy `from`'s fan-out onto `to`. Walks one chain; the body's transition
/// population is never scanned.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_copy_transitions(
    suffix_arena& arena,
    std::uint32_t from,
    std::uint32_t to) noexcept {
  for (std::uint32_t slot = arena.states.at(from).first_transition;
       slot != no_transition; slot = arena.next.at(slot)) {
    arena.lookup_steps = arena.lookup_steps + 1U;
    if (!try_link(arena, to, arena.transitions.at(slot).symbol,
            arena.transitions.at(slot).to)) {
      return false;
    }
  }
  return true;
}

/// Extend by one symbol. Returns the new end state, or `no_state` on capacity
/// refusal.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t extend(
    suffix_arena& arena,
    suffix_symbol symbol) noexcept {
  const std::uint32_t existing = transition(arena, arena.last, symbol);
  if (existing != no_state && arena.states.at(existing).maximum_length ==
          arena.states.at(arena.last).maximum_length + 1U) {
    arena.last = existing;
    arena.states.at(arena.last).material_end_multiplicity += 1U;
    return arena.last;
  }
  if (!arena.states.holds(arena.states_used)) {
    return no_state;
  }
  const std::uint32_t current = arena.states_used;
  arena.states.at(current) = suffix_state{
      arena.states.at(arena.last).maximum_length + 1U, no_state, 1, no_transition};
  arena.states_used = arena.states_used + 1U;

  std::uint32_t walk = arena.last;
  while (walk != no_state && transition(arena, walk, symbol) == no_state) {
    if (!try_link(arena, walk, symbol, current)) {
      return no_state;
    }
    walk = arena.states.at(walk).link;
  }
  if (walk == no_state) {
    arena.states.at(current).link = 0;
  } else {
    const std::uint32_t target = transition(arena, walk, symbol);
    if (arena.states.at(walk).maximum_length + 1U ==
        arena.states.at(target).maximum_length) {
      arena.states.at(current).link = target;
    } else {
      if (!arena.states.holds(arena.states_used)) {
        return no_state;
      }
      const std::uint32_t clone = arena.states_used;
      arena.states.at(clone) = suffix_state{arena.states.at(walk).maximum_length + 1U,
          arena.states.at(target).link, 0, no_transition};
      arena.states_used = arena.states_used + 1U;
      if (!try_copy_transitions(arena, target, clone)) {
        return no_state;
      }
      while (walk != no_state && transition(arena, walk, symbol) == target) {
        retarget(arena, walk, symbol, clone);
        walk = arena.states.at(walk).link;
      }
      arena.states.at(target).link = clone;
      arena.states.at(current).link = clone;
    }
  }
  arena.last = current;
  return current;
}

}  // namespace holonics::organ::suffix_law
