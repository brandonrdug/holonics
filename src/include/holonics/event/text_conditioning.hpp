#pragma once

#include <cstdint>

#include <holonics/codec/text_material.hpp>
#include <holonics/organ/incidence_arena.hpp>
#include <holonics/organ/suffix_extend.hpp>

namespace holonics::event {

struct conditioning_return final {
  std::uint32_t occurrences_crossed{};
  std::uint64_t octets_crossed{};
  std::uint32_t states{};
  std::uint32_t transitions{};
  std::uint32_t caused_admitted{};
  std::uint64_t pair_population{};
  bool complete{};
};

/// Cross a text standing into the suffix ecology and its source incidence.
///
/// Each occurrence is one informant path of octets, separated from the next so
/// no material-only path crosses between occurrences. Every prefix end state
/// admits its occurrence as a caused source, which is what makes the
/// depth-first span the complete attribution of a substring.
///
/// **The gate is structural.** This loop is linear in crossed octets. It never
/// compares one occurrence against another, so `pair_population` cannot leave
/// zero — the complete pair product the source owner refuses to enumerate has
/// no place here to be formed.
[[nodiscard]] HOLONICS_CALLABLE inline conditioning_return condition_text(
    const codec::text_arena& text,
    organ::suffix_arena& suffix,
    organ::incidence_arena& incidence,
    std::uint32_t octet_aperture) noexcept {
  conditioning_return returned{};
  for (std::uint32_t slot = 0; slot < text.occurrences_used; ++slot) {
    const codec::text_occurrence& held = text.occurrences.at(slot);
    organ::suffix_law::separate(suffix);
    const std::uint32_t crossed = held.surface_extent < octet_aperture
        ? held.surface_extent
        : octet_aperture;
    for (std::uint32_t step = 0; step < crossed; ++step) {
      const organ::suffix_symbol germ{organ::symbol_kind::germ,
          static_cast<std::uint64_t>(codec::text_law::octet(text, held, step))};
      const std::uint32_t state = organ::suffix_law::extend(suffix, germ);
      if (state == organ::no_state) {
        returned.pair_population = text.pair_population;
        return returned;
      }
      if (organ::incidence_law::try_admit(incidence, state, slot)) {
        returned.caused_admitted = returned.caused_admitted + 1U;
      }
      returned.octets_crossed = returned.octets_crossed + 1U;
    }
    if (organ::suffix_law::extend(suffix,
            organ::suffix_symbol{organ::symbol_kind::boundary, slot}) ==
        organ::no_state) {
      returned.pair_population = text.pair_population;
      return returned;
    }
    returned.occurrences_crossed = returned.occurrences_crossed + 1U;
  }
  returned.states = suffix.states_used;
  returned.transitions = suffix.transitions_used;
  returned.pair_population = text.pair_population;
  returned.complete = organ::incidence_law::freeze(incidence, suffix);
  return returned;
}

}  // namespace holonics::event
