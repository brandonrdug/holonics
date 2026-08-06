#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/resonance_germ.hpp>

namespace holonics::organ {

/// A symbol crossing the suffix ecology. A boundary separates one informant path
/// from the next so that no material-only path can cross between utterances,
/// while the automaton's suffix geometry stays valid.
enum class symbol_kind : std::uint8_t { germ, boundary };

struct suffix_symbol final {
  symbol_kind kind{symbol_kind::germ};
  std::uint64_t word{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    suffix_symbol left,
    suffix_symbol right) noexcept {
  return left.kind == right.kind && left.word == right.word;
}

inline constexpr std::uint32_t no_state = 0xFFFF'FFFFU;

/// One automaton state.
///
/// `material_end_multiplicity` counts how many distinct causal testimonies ended
/// here. **Duplicate testimony is recurrence, not redundancy**: repeated
/// passages are retained as multiplicity and are never deduplicated, and the
/// count is never normalized into a probability.
struct suffix_state final {
  std::uint32_t maximum_length{};
  std::uint32_t link{no_state};
  std::uint64_t material_end_multiplicity{};
};

struct suffix_transition final {
  std::uint32_t from{};
  std::uint32_t to{};
  suffix_symbol symbol{};
};

/// The exact suffix ecology.
///
/// A generalized suffix automaton founding **at most two states per symbol** —
/// the new end state and at most one clone — so the population stays inside the
/// exact `2N` bound rather than enumerating an n-gram powerset. It emits **no
/// root vocabulary** and holds no scores: a continuation is exposed with its
/// source state, matched length, target state, and multiplicity, and nothing
/// here selects among them.
template<std::size_t StateCapacity, std::size_t TransitionCapacity>
class suffix_automaton final {
  static_assert(StateCapacity > 1 && TransitionCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr suffix_automaton() noexcept : states_{}, transitions_{} {
    states_[0] = suffix_state{0, no_state, 0};
    used_ = 1;
    last_ = 0;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t states() const noexcept {
    return used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t transitions() const noexcept {
    return transitions_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const suffix_state* at(
      std::uint32_t state) const noexcept {
    return state < used_ ? &states_[state] : nullptr;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t transition(
      std::uint32_t from,
      suffix_symbol symbol) const noexcept {
    for (std::uint32_t slot = 0; slot < transitions_used_; ++slot) {
      if (transitions_[slot].from == from && equal(transitions_[slot].symbol, symbol)) {
        return transitions_[slot].to;
      }
    }
    return no_state;
  }

  /// Return to the root. A boundary between informant paths resets the active
  /// state so a later path cannot continue an earlier one by material alone.
  HOLONICS_CALLABLE constexpr void separate() noexcept { last_ = 0; }

  /// Extend by one symbol. Returns the new end state, or `no_state` on capacity
  /// refusal with the automaton unchanged.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t extend(
      suffix_symbol symbol) noexcept {
    const std::uint32_t existing = transition(last_, symbol);
    if (existing != no_state && states_[existing].maximum_length ==
            states_[last_].maximum_length + 1U) {
      last_ = existing;
      states_[last_].material_end_multiplicity += 1U;
      return last_;
    }
    if (used_ >= StateCapacity) {
      return no_state;
    }
    const std::uint32_t current = used_;
    states_[current] = suffix_state{states_[last_].maximum_length + 1U, no_state, 1};
    used_ = used_ + 1U;

    std::uint32_t walk = last_;
    while (walk != no_state && transition(walk, symbol) == no_state) {
      if (!try_link(walk, symbol, current)) {
        return no_state;
      }
      walk = states_[walk].link;
    }
    if (walk == no_state) {
      states_[current].link = 0;
    } else {
      const std::uint32_t target = transition(walk, symbol);
      if (states_[walk].maximum_length + 1U == states_[target].maximum_length) {
        states_[current].link = target;
      } else {
        if (used_ >= StateCapacity) {
          return no_state;
        }
        const std::uint32_t clone = used_;
        states_[clone] = suffix_state{states_[walk].maximum_length + 1U,
            states_[target].link, 0};
        used_ = used_ + 1U;
        if (!try_copy_transitions(target, clone)) {
          return no_state;
        }
        while (walk != no_state && transition(walk, symbol) == target) {
          retarget(walk, symbol, clone);
          walk = states_[walk].link;
        }
        states_[target].link = clone;
        states_[current].link = clone;
      }
    }
    last_ = current;
    return current;
  }

  /// Follow a path from the root. Returns the state reached and the matched
  /// length; an unmatched symbol returns the root with length zero rather than
  /// fabricating a continuation.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t follow(
      const suffix_symbol* path,
      std::uint32_t count,
      std::uint32_t& matched) const noexcept {
    std::uint32_t state = 0;
    matched = 0;
    for (std::uint32_t slot = 0; slot < count; ++slot) {
      const std::uint32_t next = transition(state, path[slot]);
      if (next == no_state) {
        return state;
      }
      state = next;
      matched = matched + 1U;
    }
    return state;
  }

  /// Every locally supported continuation of a state, with its multiplicity.
  /// **No score, no ranking, no selected answer** — the caller receives the
  /// whole population.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t continuations(
      std::uint32_t from,
      suffix_transition* out,
      std::uint32_t limit) const noexcept {
    std::uint32_t found = 0;
    for (std::uint32_t slot = 0; slot < transitions_used_ && found < limit; ++slot) {
      if (transitions_[slot].from == from) {
        out[found] = transitions_[slot];
        found = found + 1U;
      }
    }
    return found;
  }

 private:
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_link(
      std::uint32_t from,
      suffix_symbol symbol,
      std::uint32_t to) noexcept {
    if (transitions_used_ >= TransitionCapacity) {
      return false;
    }
    transitions_[transitions_used_] = suffix_transition{from, to, symbol};
    transitions_used_ = transitions_used_ + 1U;
    return true;
  }

  HOLONICS_CALLABLE constexpr void retarget(
      std::uint32_t from,
      suffix_symbol symbol,
      std::uint32_t to) noexcept {
    for (std::uint32_t slot = 0; slot < transitions_used_; ++slot) {
      if (transitions_[slot].from == from && equal(transitions_[slot].symbol, symbol)) {
        transitions_[slot].to = to;
        return;
      }
    }
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_copy_transitions(
      std::uint32_t from,
      std::uint32_t to) noexcept {
    const std::uint32_t before = transitions_used_;
    for (std::uint32_t slot = 0; slot < before; ++slot) {
      if (transitions_[slot].from == from &&
          !try_link(to, transitions_[slot].symbol, transitions_[slot].to)) {
        return false;
      }
    }
    return true;
  }

  suffix_state states_[StateCapacity]{};
  suffix_transition transitions_[TransitionCapacity]{};
  std::uint32_t used_{};
  std::uint32_t transitions_used_{};
  std::uint32_t last_{};
};

}  // namespace holonics::organ
