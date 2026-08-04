#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/resident_complex.hpp>

namespace holonics::structure {
namespace detail {

HOLONICS_CALLABLE constexpr void mix_hash(std::uint64_t& hash, std::uint64_t value) noexcept {
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t octet = 0; octet < 8; ++octet) {
    hash ^= value & 255U;
    hash *= prime;
    value >>= 8U;
  }
}

}  // namespace detail

HOLONICS_CALLABLE inline bool resident_complex::valid_incidence(
    const structure_case& input) const noexcept {
  for (std::size_t slot = 0; slot < input.cell_count; ++slot) {
    if (input.cells[slot].multiplicity == 0) {
      return false;
    }
  }
  std::uint16_t previous_higher = 0;
  for (std::size_t slot = 0; slot < input.incidence_count; ++slot) {
    const auto relation = input.incidences[slot];
    if (relation.higher_slot >= input.cell_count || relation.lower_slot >= input.cell_count ||
        relation.higher_slot == relation.lower_slot || relation.multiplicity == 0 ||
        (relation.orientation != -1 && relation.orientation != 1)) {
      return false;
    }
    const std::uint16_t higher_dimension = input.cells[relation.higher_slot].dimension;
    const std::uint16_t lower_dimension = input.cells[relation.lower_slot].dimension;
    if (higher_dimension != lower_dimension + 1 ||
        (slot != 0 && relation.higher_slot < previous_higher)) {
      return false;
    }
    previous_higher = relation.higher_slot;
  }
  return true;
}

HOLONICS_CALLABLE inline structure_status resident_complex::refuse_admission(
    structure_output& output,
    structure_status state) noexcept {
  output.admission.state = state;
  output.predecessor_hash = standing_hash();
  output.successor_hash = output.predecessor_hash;
  output.occurrence_mint_after = occurrence_mint_.next_serial();
  return state;
}

HOLONICS_CALLABLE inline std::size_t resident_complex::active_cell_count() const noexcept {
  std::size_t count = 0;
  for (std::size_t slot = 0; slot < cells_.used(); ++slot) {
    if (cells_.at(slot)->active()) {
      ++count;
    }
  }
  return count;
}

HOLONICS_CALLABLE inline exact::word resident_complex::standing_hash() const noexcept {
  std::uint64_t hash = 14'695'981'039'346'656'037ULL;
  detail::mix_hash(hash, static_cast<std::uint64_t>(active_cell_count()));
  for (std::size_t slot = 0; slot < cells_.used(); ++slot) {
    const resident_cell* value = cells_.at(slot);
    if (!value->active()) {
      continue;
    }
    detail::mix_hash(hash, value->occurrence().serial().value());
    detail::mix_hash(hash, value->dimension());
    detail::mix_hash(hash, value->outgoing_count());
  }
  for (std::size_t slot = 0; slot < incidences_.used(); ++slot) {
    const resident_incidence* relation = incidences_.at(slot);
    if (!relation->active()) {
      continue;
    }
    detail::mix_hash(hash, relation->higher_slot());
    detail::mix_hash(hash, relation->lower_slot());
    detail::mix_hash(hash, static_cast<std::uint8_t>(relation->orientation()));
    detail::mix_hash(hash, relation->multiplicity().value());
  }
  return exact::word{hash};
}

}  // namespace holonics::structure
