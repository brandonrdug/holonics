#include "ecology_cases.hpp"

#include <holonics/organ/source_incidence.hpp>

namespace holonics::tests {
namespace {

using holonics::organ::no_state;
using holonics::organ::suffix_symbol;
using holonics::organ::symbol_kind;

/// A deterministic germ population with genuinely shared material: consecutive
/// sources overlap by five of their eight symbols, so clones are founded and the
/// automaton does real suffix work rather than growing a disjoint forest.
[[nodiscard]] constexpr suffix_symbol germ_at(
    std::uint32_t source,
    std::uint32_t slot) noexcept {
  return suffix_symbol{symbol_kind::germ, 1U + (((source * 3U) + slot) & 0x1FU)};
}

inline constexpr std::uint32_t path_length = 8;
inline constexpr std::size_t state_capacity = 512;
inline constexpr std::size_t transition_capacity = 4096;
inline constexpr std::size_t occurrence_capacity = 256;

struct aperture_work final {
  std::uint32_t symbols{};
  std::uint32_t states{};
  std::uint64_t formation{};
  std::uint64_t lookup{};
  bool formed{};
};

/// Build, freeze, and report the work spent at one aperture.
[[nodiscard]] aperture_work cross(std::uint32_t sources) noexcept {
  aperture_work work{};
  holonics::organ::suffix_automaton<state_capacity, transition_capacity> automaton{};
  holonics::organ::source_incidence<state_capacity, occurrence_capacity> incidence{};
  for (std::uint32_t source = 0; source < sources; ++source) {
    automaton.separate();
    for (std::uint32_t slot = 0; slot < path_length; ++slot) {
      const std::uint32_t state = automaton.extend(germ_at(source, slot));
      if (state == no_state || !incidence.try_admit(state, source)) {
        return work;
      }
      work.symbols = work.symbols + 1U;
    }
    if (automaton.extend(suffix_symbol{symbol_kind::boundary, source}) == no_state) {
      return work;
    }
    work.symbols = work.symbols + 1U;
  }
  if (!incidence.freeze(automaton)) {
    return work;
  }
  work.states = automaton.states();
  work.formation = incidence.formation_steps();
  work.lookup = automaton.lookup_steps();
  work.formed = incidence.linear_cost(work.states) ==
      static_cast<std::uint64_t>(work.states) + incidence.ordered();
  return work;
}

}  // namespace

cost_return suffix_cost_law() {
  cost_return returned{};
  const aperture_work small = cross(6);
  const aperture_work large = cross(24);
  returned.small_symbols = small.symbols;
  returned.large_symbols = large.symbols;
  returned.small_states = small.states;
  returned.large_states = large.states;
  returned.small_formation = small.formation;
  returned.large_formation = large.formation;
  returned.small_lookup = small.lookup;
  returned.large_lookup = large.lookup;
  if (!small.formed || !large.formed || small.formation == 0 || small.lookup == 0) {
    return returned;
  }
  // The aperture quadruples. Linear formation and per-state lookup stay inside
  // eight; the refounded relaxation scaled near sixty and the flat transition
  // scan near sixteen. This is the falsifier of the cost law, not a benchmark.
  returned.formation_linear = large.formation <= 8U * small.formation;
  returned.lookup_linear = large.lookup <= 8U * small.lookup;
  returned.holds = returned.formation_linear && returned.lookup_linear &&
      large.symbols == 4U * small.symbols;
  return returned;
}

}  // namespace holonics::tests
