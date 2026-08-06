#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/suffix_extend.hpp>

namespace holonics::organ {

/// A fixed-capacity provider of one suffix arena.
///
/// **The laws live in `suffix_law` over `suffix_arena`, not here.** This owner
/// exists so a small declared aperture can carry its own storage inline; at
/// corpus scale the apparatus provides the same three spans out of resident
/// storage and the identical laws run over them without a frame-resident copy.
/// The two differ in who holds the pages and in nothing else.
template<std::size_t StateCapacity, std::size_t TransitionCapacity>
class suffix_automaton final {
  static_assert(StateCapacity > 1 && TransitionCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr suffix_automaton() noexcept
      : states_{}, transitions_{}, next_{} {
    arena_.states = structure::resident_span<suffix_state>{states_, StateCapacity};
    arena_.transitions =
        structure::resident_span<suffix_transition>{transitions_, TransitionCapacity};
    arena_.next = structure::resident_span<std::uint32_t>{next_, TransitionCapacity};
    static_cast<void>(suffix_law::try_found_root(arena_));
  }
  suffix_automaton(const suffix_automaton&) = delete;
  suffix_automaton& operator=(const suffix_automaton&) = delete;
  suffix_automaton(suffix_automaton&&) = delete;
  suffix_automaton& operator=(suffix_automaton&&) = delete;

  /// The arena this owner provides. The interior operates through this view.
  [[nodiscard]] HOLONICS_CALLABLE constexpr suffix_arena& arena() noexcept {
    return arena_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const suffix_arena& arena() const noexcept {
    return arena_;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t states() const noexcept {
    return arena_.states_used;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t transitions() const noexcept {
    return arena_.transitions_used;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const suffix_state* at(
      std::uint32_t state) const noexcept {
    return suffix_law::state_at(arena_, state);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t lookup_steps() const noexcept {
    return arena_.lookup_steps;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t transition(
      std::uint32_t from,
      suffix_symbol symbol) noexcept {
    return suffix_law::transition(arena_, from, symbol);
  }
  HOLONICS_CALLABLE constexpr void separate() noexcept { suffix_law::separate(arena_); }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t extend(
      suffix_symbol symbol) noexcept {
    return suffix_law::extend(arena_, symbol);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t follow(
      const suffix_symbol* path,
      std::uint32_t count,
      std::uint32_t& matched) noexcept {
    return suffix_law::follow(arena_, path, count, matched);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t continuations(
      std::uint32_t from,
      suffix_transition* out,
      std::uint32_t limit) const noexcept {
    return suffix_law::continuations(arena_, from, out, limit);
  }

 private:
  suffix_state states_[StateCapacity]{};
  suffix_transition transitions_[TransitionCapacity]{};
  std::uint32_t next_[TransitionCapacity]{};
  suffix_arena arena_{};
};

}  // namespace holonics::organ
