#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/incidence_arena.hpp>
#include <holonics/organ/suffix_automaton.hpp>

namespace holonics::organ {

/// A fixed-capacity provider of one incidence arena.
///
/// **The laws live in `incidence_law` over `incidence_arena`, not here.** This
/// owner carries its own pages for a small declared aperture; at corpus scale
/// the apparatus provides the same eight spans out of resident storage and the
/// identical laws run over them.
template<std::size_t StateCapacity, std::size_t OccurrenceCapacity>
class source_incidence final {
  static_assert(StateCapacity > 0 && OccurrenceCapacity > 0);

 public:
  HOLONICS_CALLABLE constexpr source_incidence() noexcept
      : staged_{}, staged_next_{}, ordered_sources_{}, spans_{}, direct_head_{},
        first_child_{}, next_sibling_{}, walk_stack_{} {
    arena_.staged =
        structure::resident_span<source_occurrence>{staged_, OccurrenceCapacity};
    arena_.staged_next =
        structure::resident_span<std::uint32_t>{staged_next_, OccurrenceCapacity};
    arena_.ordered_sources =
        structure::resident_span<std::uint32_t>{ordered_sources_, OccurrenceCapacity};
    arena_.spans = structure::resident_span<source_span>{spans_, StateCapacity};
    arena_.direct_head =
        structure::resident_span<std::uint32_t>{direct_head_, StateCapacity};
    arena_.first_child =
        structure::resident_span<std::uint32_t>{first_child_, StateCapacity};
    arena_.next_sibling =
        structure::resident_span<std::uint32_t>{next_sibling_, StateCapacity};
    arena_.walk_stack =
        structure::resident_span<std::uint32_t>{walk_stack_, StateCapacity};
    static_cast<void>(incidence_law::try_open(arena_));
  }
  source_incidence(const source_incidence&) = delete;
  source_incidence& operator=(const source_incidence&) = delete;
  source_incidence(source_incidence&&) = delete;
  source_incidence& operator=(source_incidence&&) = delete;

  [[nodiscard]] HOLONICS_CALLABLE constexpr incidence_arena& arena() noexcept {
    return arena_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr const incidence_arena& arena() const noexcept {
    return arena_;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t occurrences() const noexcept {
    return arena_.staged_used;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t ordered() const noexcept {
    return arena_.ordered_used;
  }
  /// One source in depth-first emission order. The state it belongs to is
  /// implied by the span that covers it — no per-occurrence state is retained
  /// after formation.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t ordered_source(
      std::uint32_t slot) const noexcept {
    return slot < arena_.ordered_used ? arena_.ordered_sources.at(slot) : no_state;
  }
  /// Steps spent forming the incidence. Physical testimony; it enters no
  /// admission, no ordering, and no return.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t formation_steps() const noexcept {
    return arena_.formation_steps;
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool try_admit(
      std::uint32_t state,
      std::uint32_t source) noexcept {
    return incidence_law::try_admit(arena_, state, source);
  }

  template<std::size_t TransitionCapacity>
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool freeze(
      const suffix_automaton<StateCapacity, TransitionCapacity>& automaton) noexcept {
    return incidence_law::freeze(arena_, automaton.arena());
  }

  [[nodiscard]] HOLONICS_CALLABLE constexpr source_span span(
      std::uint32_t state) const noexcept {
    return incidence_law::span(arena_, state);
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr bool reaches(
      std::uint32_t state,
      std::uint32_t source) const noexcept {
    return incidence_law::reaches(arena_, state, source);
  }

  /// The storage this attribution costs. Linear in states plus caused
  /// occurrences; the refused alternative would have been their product.
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t linear_cost(
      std::uint32_t states) const noexcept {
    return static_cast<std::uint64_t>(states) +
        static_cast<std::uint64_t>(arena_.ordered_used);
  }

 private:
  source_occurrence staged_[OccurrenceCapacity]{};
  std::uint32_t staged_next_[OccurrenceCapacity]{};
  std::uint32_t ordered_sources_[OccurrenceCapacity]{};
  source_span spans_[StateCapacity]{};
  std::uint32_t direct_head_[StateCapacity]{};
  std::uint32_t first_child_[StateCapacity]{};
  std::uint32_t next_sibling_[StateCapacity]{};
  std::uint32_t walk_stack_[StateCapacity]{};
  incidence_arena arena_{};
};

}  // namespace holonics::organ
