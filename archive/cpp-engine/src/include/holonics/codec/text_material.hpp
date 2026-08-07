#pragma once

#include <cstdint>

#include <holonics/structure/resident_span.hpp>

namespace holonics::codec {

enum class text_role : std::uint8_t { document, human, assistant };
enum class text_phase : std::uint8_t { received, final_answer, emanated };

enum class text_admission : std::uint8_t {
  founded,
  version_founded,
  duplicate_testimony,
  surface_refused,
  capacity_refused,
  ordering_refused
};

/// One text occurrence.
///
/// **Identity is version-specific and is decided by exact surface comparison,
/// never by a digest.** Equal native identity with a different surface remains
/// plural: the earlier version stays readable and the later one is a version
/// fiber, which is the reflective runtime's parented-codec law at corpus scale.
/// A digest would decide the same question by collision-bounded proxy; the
/// retained surface decides it exactly.
///
/// `caused_count` may be zero. **Corpus adjacency is not ancestry** — an
/// occurrence whose causing witnesses were not supplied leaves its causal fiber
/// OPEN rather than adopting whatever was admitted before it.
struct text_occurrence final {
  std::uint64_t native_identity{};
  std::uint32_t version{};
  std::uint32_t surface_start{};
  std::uint32_t surface_extent{};
  std::uint32_t container{};
  std::uint32_t ordinal{};
  std::uint64_t witness_multiplicity{};
  std::uint32_t caused_start{};
  std::uint32_t caused_count{};
  text_role role{text_role::document};
  text_phase phase{text_phase::received};
};

/// The exact text standing, held in resident storage it does not own.
///
/// `pair_population` is the admission gate the source owner states literally: it
/// must remain zero, because **no pairwise product over occurrences is ever
/// enumerated**. Any law that compared occurrence against occurrence would
/// increment it, and a mount that returns non-zero has built the complete pair
/// product the port exists to refuse.
struct text_arena final {
  structure::resident_span<unsigned char> surface{};
  structure::resident_span<text_occurrence> occurrences{};
  structure::resident_span<std::uint32_t> caused{};
  std::uint32_t surface_used{};
  std::uint32_t occurrences_used{};
  std::uint32_t caused_used{};
  std::uint64_t pair_population{};
  std::uint64_t duplicate_witnesses{};
  std::uint64_t version_fibers{};
  std::uint64_t open_causal_fibers{};
};

namespace text_law {

/// The native identity of one section of one container. Sections are ordered
/// within a container, so occurrences sharing a native identity are adjacent and
/// the plurality decision is local — it never scans the population.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t native_identity(
    std::uint32_t container,
    std::uint32_t section) noexcept {
  return (static_cast<std::uint64_t>(container) << 20U) |
      static_cast<std::uint64_t>(section & 0xFFFFFU);
}

/// Exact surface comparison against one retained occurrence.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_surface(
    const text_arena& arena,
    const text_occurrence& standing,
    const unsigned char* bytes,
    std::uint32_t extent) noexcept {
  if (standing.surface_extent != extent) {
    return false;
  }
  for (std::uint32_t slot = 0; slot < extent; ++slot) {
    if (arena.surface.at(standing.surface_start + slot) != bytes[slot]) {
      return false;
    }
  }
  return true;
}

/// Admit one section.
///
/// The only comparison performed is against the immediately preceding
/// occurrence, and only when it carries the same native identity. Nothing here
/// forms a pair over the population.
[[nodiscard]] HOLONICS_CALLABLE constexpr text_admission try_admit(
    text_arena& arena,
    std::uint32_t container,
    std::uint32_t section,
    text_role role,
    text_phase phase,
    const unsigned char* bytes,
    std::uint32_t extent,
    const std::uint32_t* caused_by,
    std::uint32_t caused_count) noexcept {
  if (bytes == nullptr || extent == 0) {
    return text_admission::surface_refused;
  }
  const std::uint64_t native = native_identity(container, section);
  if (arena.occurrences_used != 0) {
    const text_occurrence& previous = arena.occurrences.at(arena.occurrences_used - 1U);
    if (previous.native_identity > native) {
      return text_admission::ordering_refused;
    }
    if (previous.native_identity == native &&
        same_surface(arena, previous, bytes, extent)) {
      arena.occurrences.at(arena.occurrences_used - 1U).witness_multiplicity += 1U;
      arena.duplicate_witnesses = arena.duplicate_witnesses + 1U;
      return text_admission::duplicate_testimony;
    }
  }
  if (!arena.occurrences.holds(arena.occurrences_used) ||
      !arena.surface.holds(arena.surface_used + extent - 1U) ||
      (caused_count != 0 && !arena.caused.holds(arena.caused_used + caused_count - 1U))) {
    return text_admission::capacity_refused;
  }
  const bool versioned = arena.occurrences_used != 0 &&
      arena.occurrences.at(arena.occurrences_used - 1U).native_identity == native;
  text_occurrence minted{};
  minted.native_identity = native;
  minted.version = versioned
      ? arena.occurrences.at(arena.occurrences_used - 1U).version + 1U
      : 0U;
  minted.surface_start = arena.surface_used;
  minted.surface_extent = extent;
  minted.container = container;
  minted.ordinal = arena.occurrences_used;
  minted.witness_multiplicity = 1;
  minted.caused_start = arena.caused_used;
  minted.caused_count = caused_count;
  minted.role = role;
  minted.phase = phase;
  for (std::uint32_t slot = 0; slot < extent; ++slot) {
    arena.surface.at(arena.surface_used + slot) = bytes[slot];
  }
  arena.surface_used = arena.surface_used + extent;
  for (std::uint32_t slot = 0; slot < caused_count; ++slot) {
    arena.caused.at(arena.caused_used + slot) = caused_by[slot];
  }
  arena.caused_used = arena.caused_used + caused_count;
  arena.occurrences.at(arena.occurrences_used) = minted;
  arena.occurrences_used = arena.occurrences_used + 1U;
  if (versioned) {
    arena.version_fibers = arena.version_fibers + 1U;
  }
  if (caused_count == 0) {
    arena.open_causal_fibers = arena.open_causal_fibers + 1U;
  }
  return versioned ? text_admission::version_founded : text_admission::founded;
}

/// Read one octet of one occurrence's surface. This is the only way the
/// conditioning reaches text, so the material stays in resident storage.
[[nodiscard]] HOLONICS_CALLABLE constexpr unsigned char octet(
    const text_arena& arena,
    const text_occurrence& occurrence,
    std::uint32_t slot) noexcept {
  return arena.surface.at(occurrence.surface_start + slot);
}

}  // namespace text_law

}  // namespace holonics::codec
