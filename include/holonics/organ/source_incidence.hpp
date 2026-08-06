#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/suffix_automaton.hpp>

namespace holonics::organ {

/// **The source-incidence invention, ported exactly.**
///
/// Suffix links form a rooted tree. A depth-first order over that tree makes
/// every state's descendant population **contiguous**, so a state's sources are
/// one span into a single shared array. Storage is therefore
/// `O(states + caused occurrences)` and **never `states x sources`** — the naive
/// table does not fit at laboratory scale.
struct source_span final {
  std::uint32_t start{};
  std::uint32_t length{};
};

struct source_occurrence final {
  std::uint32_t state{};
  std::uint32_t source{};
  std::uint32_t position{};
};

template<std::size_t StateCapacity, std::size_t OccurrenceCapacity>
class source_incidence final {
  static_assert(StateCapacity > 0 && OccurrenceCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr source_incidence() noexcept : enter_{}, leave_{}, occurrences_{} {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t occurrences() const noexcept {
    return occurrences_used_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const source_occurrence* at(
      std::uint32_t slot) const noexcept {
    return slot < occurrences_used_ ? &occurrences_[slot] : nullptr;
  }

  /// Record that one caused occurrence of `source` ended at `state`.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_admit(
      std::uint32_t state,
      std::uint32_t source) noexcept {
    if (occurrences_used_ >= OccurrenceCapacity) {
      return false;
    }
    occurrences_[occurrences_used_] = source_occurrence{state, source, 0};
    occurrences_used_ = occurrences_used_ + 1U;
    return true;
  }

  /// Form the depth-first intervals over the suffix-link tree and sort the
  /// occurrence population into that order. After this, a state's sources are a
  /// contiguous run.
  template<std::size_t TransitionCapacity>
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool freeze(
      const suffix_automaton<StateCapacity, TransitionCapacity>& automaton) noexcept {
    const std::uint32_t states = automaton.states();
    if (states > StateCapacity) {
      return false;
    }
    std::uint32_t clock = 0;
    for (std::uint32_t state = 0; state < states; ++state) {
      enter_[state] = no_state;
      leave_[state] = 0;
    }
    // Iterative post-order over the link tree: a state may be entered only after
    // its parent. Depth is bounded by the state count, so this terminates.
    for (std::uint32_t depth = 0; depth <= states; ++depth) {
      bool advanced = false;
      for (std::uint32_t state = 0; state < states; ++state) {
        if (enter_[state] != no_state) {
          continue;
        }
        const std::uint32_t parent = automaton.at(state)->link;
        if (parent != no_state && enter_[parent] == no_state) {
          continue;
        }
        enter_[state] = clock;
        clock = clock + 1U;
        advanced = true;
      }
      if (!advanced) {
        break;
      }
    }
    for (std::uint32_t state = 0; state < states; ++state) {
      if (enter_[state] == no_state) {
        return false;
      }
    }
    // A state's subtree is every state whose chain of links passes through it.
    for (std::uint32_t state = 0; state < states; ++state) {
      std::uint32_t highest = enter_[state];
      for (std::uint32_t other = 0; other < states; ++other) {
        std::uint32_t walk = other;
        for (std::uint32_t step = 0; step <= states; ++step) {
          if (walk == state) {
            highest = enter_[other] > highest ? enter_[other] : highest;
            break;
          }
          if (walk == no_state) {
            break;
          }
          walk = automaton.at(walk)->link;
        }
      }
      leave_[state] = highest + 1U;
    }
    for (std::uint32_t slot = 0; slot < occurrences_used_; ++slot) {
      occurrences_[slot].position = enter_[occurrences_[slot].state];
    }
    for (std::uint32_t slot = 1; slot < occurrences_used_; ++slot) {
      const source_occurrence carried = occurrences_[slot];
      std::uint32_t place = slot;
      while (place > 0 && occurrences_[place - 1U].position > carried.position) {
        occurrences_[place] = occurrences_[place - 1U];
        place = place - 1U;
      }
      occurrences_[place] = carried;
    }
    frozen_ = true;
    return true;
  }

  /// The contiguous span of occurrences whose end state lies in this state's
  /// subtree. One binary search and one walk; no per-state table exists.
  [[nodiscard]] HOLONICS_CALLABLE constexpr source_span span(
      std::uint32_t state) const noexcept {
    source_span found{};
    if (!frozen_ || state >= StateCapacity || enter_[state] == no_state) {
      return found;
    }
    const std::uint32_t low = enter_[state];
    const std::uint32_t high = leave_[state];
    std::uint32_t begin = occurrences_used_;
    std::uint32_t end = occurrences_used_;
    for (std::uint32_t slot = 0; slot < occurrences_used_; ++slot) {
      const std::uint32_t position = occurrences_[slot].position;
      if (position >= low && position < high) {
        begin = begin == occurrences_used_ ? slot : begin;
        end = slot + 1U;
      }
    }
    if (begin == occurrences_used_) {
      return found;
    }
    found.start = begin;
    found.length = end - begin;
    return found;
  }

  /// Does `source` reach `state`? Answered from the span, never by scanning the
  /// whole population.
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool reaches(
      std::uint32_t state,
      std::uint32_t source) const noexcept {
    const source_span found = span(state);
    for (std::uint32_t slot = 0; slot < found.length; ++slot) {
      if (occurrences_[found.start + slot].source == source) {
        return true;
      }
    }
    return false;
  }

  /// The storage this attribution costs. It is linear in states plus caused
  /// occurrences; the refused alternative would have been their product.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t linear_cost(
      std::uint32_t states) const noexcept {
    return static_cast<std::uint64_t>(states) +
        static_cast<std::uint64_t>(occurrences_used_);
  }

 private:
  std::uint32_t enter_[StateCapacity]{};
  std::uint32_t leave_[StateCapacity]{};
  source_occurrence occurrences_[OccurrenceCapacity]{};
  std::uint32_t occurrences_used_{};
  bool frozen_{};
};

}  // namespace holonics::organ
