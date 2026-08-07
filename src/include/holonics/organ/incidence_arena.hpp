#pragma once

#include <cstdint>

#include <holonics/organ/suffix_arena.hpp>

namespace holonics::organ {

struct source_span final {
  std::uint32_t start{};
  std::uint32_t length{};
};

struct source_occurrence final {
  std::uint32_t state{};
  std::uint32_t source{};
};

/// **The source-incidence invention, with its cost law.**
///
/// Suffix links form a rooted tree. A single depth-first walk over that tree
/// makes every state's descendant population **contiguous**, so a state's
/// sources are one stored span into one shared array. Storage is
/// `O(states + caused occurrences)` and **never `states x sources`**; formation
/// is one `O(states)` child-chain build plus one `O(states + occurrences)` walk;
/// and a span is read, not searched.
///
/// This mirrors `SourceIncidence::from_suffix_tree` at checkpoint `93834398`
/// (`suffix_ecology.rs:338-395`). Like the suffix arena, it holds spans it does
/// not own, so attribution over a corpus never enters a kernel frame.
struct incidence_arena final {
  structure::resident_span<source_occurrence> staged{};
  structure::resident_span<std::uint32_t> staged_next{};
  structure::resident_span<std::uint32_t> ordered_sources{};
  structure::resident_span<source_span> spans{};
  structure::resident_span<std::uint32_t> direct_head{};
  structure::resident_span<std::uint32_t> first_child{};
  structure::resident_span<std::uint32_t> next_sibling{};
  structure::resident_span<std::uint32_t> walk_stack{};
  std::uint32_t staged_used{};
  std::uint32_t ordered_used{};
  std::uint64_t formation_steps{};
  bool frozen{};
};

namespace incidence_law {

/// Clear the per-state chains. An arena without storage refuses.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_open(incidence_arena& arena) noexcept {
  if (!arena.staged.present() || !arena.spans.present() ||
      arena.staged_next.extent != arena.staged.extent ||
      arena.ordered_sources.extent != arena.staged.extent ||
      arena.direct_head.extent != arena.spans.extent ||
      arena.first_child.extent != arena.spans.extent ||
      arena.next_sibling.extent != arena.spans.extent ||
      arena.walk_stack.extent != arena.spans.extent) {
    return false;
  }
  for (std::uint32_t slot = 0; slot < arena.spans.extent; ++slot) {
    arena.direct_head.at(slot) = no_child;
    arena.first_child.at(slot) = no_child;
    arena.next_sibling.at(slot) = no_child;
  }
  arena.staged_used = 0;
  arena.ordered_used = 0;
  arena.frozen = false;
  return true;
}

/// Record that one caused occurrence of `source` ended at `state`. Constant
/// work: the occurrence is prepended to that state's own direct chain, so
/// formation never has to search for it.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_admit(
    incidence_arena& arena,
    std::uint32_t state,
    std::uint32_t source) noexcept {
  if (!arena.staged.holds(arena.staged_used) || !arena.direct_head.holds(state)) {
    return false;
  }
  arena.staged.at(arena.staged_used) = source_occurrence{state, source};
  arena.staged_next.at(arena.staged_used) = arena.direct_head.at(state);
  arena.direct_head.at(state) = arena.staged_used;
  arena.staged_used = arena.staged_used + 1U;
  return true;
}

/// Emit one state's direct sources. The chain is walked in reverse admission
/// order, which is deterministic; span membership does not depend on order
/// within a state.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool emit_direct(
    incidence_arena& arena,
    std::uint32_t state) noexcept {
  for (std::uint32_t slot = arena.direct_head.at(state); slot != no_child;
       slot = arena.staged_next.at(slot)) {
    if (!arena.ordered_sources.holds(arena.ordered_used)) {
      return false;
    }
    arena.ordered_sources.at(arena.ordered_used) = arena.staged.at(slot).source;
    arena.ordered_used = arena.ordered_used + 1U;
    arena.formation_steps = arena.formation_steps + 1U;
  }
  return true;
}

/// Form the depth-first spans over the suffix-link tree.
///
/// One pass builds `first_child` / `next_sibling` from the links. One explicit
/// stack then walks the tree, emitting each state's direct sources at the moment
/// it is entered and closing its span when it is left. Every state is pushed
/// exactly once and every staged occurrence is emitted exactly once.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool freeze(
    incidence_arena& arena,
    const suffix_arena& automaton) noexcept {
  const std::uint32_t states = automaton.states_used;
  if (states == 0 || states > arena.spans.extent ||
      automaton.states.at(0).link != no_state) {
    return false;
  }
  for (std::uint32_t state = 0; state < states; ++state) {
    arena.first_child.at(state) = no_child;
    arena.next_sibling.at(state) = no_child;
    arena.spans.at(state) = source_span{};
    arena.formation_steps = arena.formation_steps + 1U;
  }
  for (std::uint32_t state = 1; state < states; ++state) {
    const std::uint32_t parent = automaton.states.at(state).link;
    if (parent == no_state || parent >= states || parent == state) {
      return false;
    }
    arena.next_sibling.at(state) = arena.first_child.at(parent);
    arena.first_child.at(parent) = state;
    arena.formation_steps = arena.formation_steps + 1U;
  }
  arena.ordered_used = 0;
  if (!emit_direct(arena, 0)) {
    return false;
  }
  arena.walk_stack.at(0) = 0;
  std::uint32_t depth = 1;
  while (depth > 0) {
    const std::uint32_t state = arena.walk_stack.at(depth - 1U);
    arena.formation_steps = arena.formation_steps + 1U;
    const std::uint32_t child = arena.first_child.at(state);
    if (child != no_child) {
      arena.first_child.at(state) = arena.next_sibling.at(child);
      arena.spans.at(child).start = arena.ordered_used;
      if (!emit_direct(arena, child) || !arena.walk_stack.holds(depth)) {
        return false;
      }
      arena.walk_stack.at(depth) = child;
      depth = depth + 1U;
      continue;
    }
    arena.spans.at(state).length = arena.ordered_used - arena.spans.at(state).start;
    depth = depth - 1U;
  }
  if (arena.ordered_used != arena.staged_used) {
    return false;
  }
  arena.frozen = true;
  return true;
}

/// The contiguous span of sources whose end state lies in this state's subtree.
/// **Read, not searched** — the depth-first walk already knew it.
[[nodiscard]] HOLONICS_CALLABLE constexpr source_span span(
    const incidence_arena& arena,
    std::uint32_t state) noexcept {
  return arena.frozen && arena.spans.holds(state) ? arena.spans.at(state)
                                                  : source_span{};
}

/// Does `source` reach `state`? Answered inside that state's span, never by
/// scanning the occurrence population.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool reaches(
    const incidence_arena& arena,
    std::uint32_t state,
    std::uint32_t source) noexcept {
  const source_span found = span(arena, state);
  for (std::uint32_t slot = 0; slot < found.length; ++slot) {
    if (arena.ordered_sources.at(found.start + slot) == source) {
      return true;
    }
  }
  return false;
}

}  // namespace incidence_law

}  // namespace holonics::organ
