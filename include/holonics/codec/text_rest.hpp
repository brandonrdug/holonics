#pragma once

#include <cstdint>

#include <holonics/codec/text_material.hpp>

namespace holonics::codec {

inline constexpr std::uint64_t text_rest_schema = 0x484F'4C54'5854'0001ULL;
inline constexpr std::uint32_t text_rest_header_octets = 64;
inline constexpr std::uint32_t text_occurrence_octets = 48;

/// The native rest of one text standing.
///
/// The image is `[header][surface][occurrences][caused]`. A remount founds a
/// fresh host from these octets **and nothing else** — no container is reopened,
/// no section is re-split, no developmental source is consulted. That is the law
/// the source owner states at `resident.rs:127`, and it is what makes the rested
/// body the same body rather than a rebuild that happens to agree.
struct text_rest_extent final {
  std::uint32_t header{text_rest_header_octets};
  std::uint32_t surface{};
  std::uint32_t occurrences{};
  std::uint32_t caused{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t total() const noexcept {
    return header + surface + occurrences + caused;
  }
};

namespace text_rest_law {

HOLONICS_CALLABLE constexpr void put_word(
    unsigned char* image,
    std::uint32_t at,
    std::uint64_t value) noexcept {
  for (std::uint32_t octet = 0; octet < 8U; ++octet) {
    image[at + octet] = static_cast<unsigned char>((value >> (octet * 8U)) & 0xFFU);
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t take_word(
    const unsigned char* image,
    std::uint32_t at) noexcept {
  std::uint64_t value = 0;
  for (std::uint32_t octet = 0; octet < 8U; ++octet) {
    value |= static_cast<std::uint64_t>(image[at + octet]) << (octet * 8U);
  }
  return value;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr text_rest_extent extent_of(
    const text_arena& arena) noexcept {
  text_rest_extent extent{};
  extent.surface = arena.surface_used;
  extent.occurrences = arena.occurrences_used * text_occurrence_octets;
  extent.caused = arena.caused_used * 4U;
  return extent;
}

/// Encode. Returns the written extent, or zero on a short image.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t encode(
    const text_arena& arena,
    unsigned char* image,
    std::uint32_t capacity) noexcept {
  const text_rest_extent extent = extent_of(arena);
  if (image == nullptr || capacity < extent.total()) {
    return 0;
  }
  for (std::uint32_t slot = 0; slot < text_rest_header_octets; ++slot) {
    image[slot] = 0;
  }
  put_word(image, 0, text_rest_schema);
  put_word(image, 8, arena.surface_used);
  put_word(image, 16, arena.occurrences_used);
  put_word(image, 24, arena.caused_used);
  put_word(image, 32, arena.duplicate_witnesses);
  put_word(image, 40, arena.version_fibers);
  put_word(image, 48, arena.open_causal_fibers);
  put_word(image, 56, arena.pair_population);
  std::uint32_t at = text_rest_header_octets;
  for (std::uint32_t slot = 0; slot < arena.surface_used; ++slot) {
    image[at + slot] = arena.surface.at(slot);
  }
  at = at + arena.surface_used;
  for (std::uint32_t slot = 0; slot < arena.occurrences_used; ++slot) {
    const text_occurrence& held = arena.occurrences.at(slot);
    const std::uint32_t base = at + (slot * text_occurrence_octets);
    put_word(image, base, held.native_identity);
    put_word(image, base + 8, held.version);
    put_word(image, base + 16, held.surface_start);
    put_word(image, base + 24, held.surface_extent);
    put_word(image, base + 32, held.witness_multiplicity);
    put_word(image, base + 40,
        (static_cast<std::uint64_t>(held.container) << 32U) |
            static_cast<std::uint64_t>(held.caused_count));
    image[base + 46] = static_cast<unsigned char>(held.role);
    image[base + 47] = static_cast<unsigned char>(held.phase);
  }
  at = at + extent.occurrences;
  for (std::uint32_t slot = 0; slot < arena.caused_used; ++slot) {
    const std::uint32_t base = at + (slot * 4U);
    const std::uint32_t held = arena.caused.at(slot);
    for (std::uint32_t octet = 0; octet < 4U; ++octet) {
      image[base + octet] = static_cast<unsigned char>((held >> (octet * 8U)) & 0xFFU);
    }
  }
  return extent.total();
}

/// Found a fresh standing from native octets alone. The arena's spans must
/// already be reserved; nothing else is consulted.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool decode(
    text_arena& arena,
    const unsigned char* image,
    std::uint32_t extent) noexcept {
  if (image == nullptr || extent < text_rest_header_octets ||
      take_word(image, 0) != text_rest_schema) {
    return false;
  }
  const std::uint32_t surface = static_cast<std::uint32_t>(take_word(image, 8));
  const std::uint32_t occurrences = static_cast<std::uint32_t>(take_word(image, 16));
  const std::uint32_t caused = static_cast<std::uint32_t>(take_word(image, 24));
  if (surface > arena.surface.extent || occurrences > arena.occurrences.extent ||
      caused > arena.caused.extent ||
      extent < text_rest_header_octets + surface +
          (occurrences * text_occurrence_octets) + (caused * 4U)) {
    return false;
  }
  arena.duplicate_witnesses = take_word(image, 32);
  arena.version_fibers = take_word(image, 40);
  arena.open_causal_fibers = take_word(image, 48);
  arena.pair_population = take_word(image, 56);
  std::uint32_t at = text_rest_header_octets;
  for (std::uint32_t slot = 0; slot < surface; ++slot) {
    arena.surface.at(slot) = image[at + slot];
  }
  at = at + surface;
  std::uint32_t caused_at = 0;
  for (std::uint32_t slot = 0; slot < occurrences; ++slot) {
    const std::uint32_t base = at + (slot * text_occurrence_octets);
    text_occurrence held{};
    held.native_identity = take_word(image, base);
    held.version = static_cast<std::uint32_t>(take_word(image, base + 8));
    held.surface_start = static_cast<std::uint32_t>(take_word(image, base + 16));
    held.surface_extent = static_cast<std::uint32_t>(take_word(image, base + 24));
    held.witness_multiplicity = take_word(image, base + 32);
    const std::uint64_t packed = take_word(image, base + 40) & 0xFFFF'FFFF'FFFFULL;
    held.container = static_cast<std::uint32_t>(packed >> 32U);
    held.caused_count = static_cast<std::uint32_t>(packed & 0xFFFF'FFFFULL);
    held.ordinal = slot;
    held.caused_start = caused_at;
    caused_at = caused_at + held.caused_count;
    held.role = static_cast<text_role>(image[base + 46]);
    held.phase = static_cast<text_phase>(image[base + 47]);
    arena.occurrences.at(slot) = held;
  }
  at = at + (occurrences * text_occurrence_octets);
  for (std::uint32_t slot = 0; slot < caused; ++slot) {
    const std::uint32_t base = at + (slot * 4U);
    std::uint32_t held = 0;
    for (std::uint32_t octet = 0; octet < 4U; ++octet) {
      held |= static_cast<std::uint32_t>(image[base + octet]) << (octet * 8U);
    }
    arena.caused.at(slot) = held;
  }
  arena.surface_used = surface;
  arena.occurrences_used = occurrences;
  arena.caused_used = caused;
  return true;
}

/// Is the later image the earlier one advanced by a bounded delta?
///
/// Each payload region of the earlier rest must be an exact prefix of the same
/// region in the later rest. **The card may then advance by appending those
/// octets rather than re-forming the body**, which is what forbids a hot device
/// path from replaying the complete host algorithm.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool append_stable(
    const unsigned char* earlier,
    const unsigned char* later) noexcept {
  if (earlier == nullptr || later == nullptr) {
    return false;
  }
  const std::uint32_t regions[3] = {8, 16, 24};
  std::uint32_t earlier_at = text_rest_header_octets;
  std::uint32_t later_at = text_rest_header_octets;
  const std::uint32_t widths[3] = {1, text_occurrence_octets, 4};
  for (std::uint32_t region = 0; region < 3U; ++region) {
    const std::uint32_t earlier_count =
        static_cast<std::uint32_t>(take_word(earlier, regions[region]));
    const std::uint32_t later_count =
        static_cast<std::uint32_t>(take_word(later, regions[region]));
    if (later_count < earlier_count) {
      return false;
    }
    const std::uint32_t held = earlier_count * widths[region];
    for (std::uint32_t slot = 0; slot < held; ++slot) {
      if (earlier[earlier_at + slot] != later[later_at + slot]) {
        return false;
      }
    }
    earlier_at = earlier_at + held;
    later_at = later_at + (later_count * widths[region]);
  }
  return true;
}

}  // namespace text_rest_law

}  // namespace holonics::codec
