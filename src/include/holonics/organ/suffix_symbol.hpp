#pragma once

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

/// The canonical order on symbols: germ material before separators, then by
/// word. A state's fan-out is held in this order, so a germ lookup never walks
/// the separator population — and separators are necessarily one per informant
/// path, which is the only fan-out that grows with the source population.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool precedes(
    suffix_symbol left,
    suffix_symbol right) noexcept {
  return left.kind != right.kind ? left.kind < right.kind : left.word < right.word;
}

inline constexpr std::uint32_t no_state = 0xFFFF'FFFFU;

/// The empty slot of a per-state transition chain. Distinct from `no_state`
/// because it indexes the transition population, not the state population.
inline constexpr std::uint32_t no_transition = 0xFFFF'FFFFU;

/// The empty slot of a suffix-link child chain.
inline constexpr std::uint32_t no_child = 0xFFFF'FFFFU;

}  // namespace holonics::organ
