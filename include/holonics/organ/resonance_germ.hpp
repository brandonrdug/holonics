#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/organ/receiver_fiber.hpp>

namespace holonics::organ {

inline constexpr std::size_t germ_capacity = 16;

/// An exact receiver-local pattern.
///
/// `identity` is the material morphology by which separated informants may
/// become eligible to meet. `phase` is its local geometric presentation.
/// **Equal identity with incompatible phase remains an OPEN comparison rather
/// than being averaged.** That refusal is the whole point of carrying phase
/// separately from identity.
struct resonance_germ final {
  receiver_fiber_identity identity{};
  std::uint64_t phase{};
};

/// Receptor roles. The registry keys on these so that a germ receptor, an
/// informant marker, and an informant capacity at the same identity remain three
/// distinct continuing capabilities.
inline constexpr std::uint32_t germ_receptor = 1;
inline constexpr std::uint32_t informant_marker_receptor = 2;
inline constexpr std::uint32_t informant_capacity_receptor = 3;

/// The registry key. **The registry contains no informant pairs, no targets, no
/// scores, and no returned deeds** — only the exact `(role, identity, phase)`
/// under which one persistent receptor current stands.
struct receptor_key final {
  std::uint32_t role{};
  receiver_fiber_identity identity{};
  std::uint64_t phase{};
};

/// A caused information occurrence.
///
/// Its germ population is a **hyperedge**: the occurrence declares only that
/// these local sections belong to this informant. **Cross-informant relation is
/// absent until matching boundaries actually close through the Swing.** Nothing
/// here asserts that two informants are related; the registry cannot express it.
struct resonance_occurrence final {
  receiver_fiber_identity informant{};
  resonance_germ germs[germ_capacity]{};
  std::uint8_t germ_count{};
  std::uint64_t source_order{};
  occurrence_origin origin{occurrence_origin::inherited};
  bool has_informant{};
  bool continuation_exposure{};
  bool path_continuations{};
};

namespace germ_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(
    const resonance_germ& germ) noexcept {
  return fiber_law::admitted(germ.identity);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr receptor_key key_of(
    const resonance_germ& germ) noexcept {
  return receptor_key{germ_receptor, germ.identity, germ.phase};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr receptor_key informant_key(
    std::uint32_t role,
    const receiver_fiber_identity& identity,
    std::uint64_t phase) noexcept {
  return receptor_key{role, identity, phase};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const receptor_key& left,
    const receptor_key& right) noexcept {
  return left.role == right.role && left.phase == right.phase &&
      fiber_law::equal(left.identity, right.identity);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool precedes(
    const receptor_key& left,
    const receptor_key& right) noexcept {
  if (left.role != right.role) {
    return left.role < right.role;
  }
  if (!fiber_law::equal(left.identity, right.identity)) {
    return fiber_law::precedes(left.identity, right.identity);
  }
  return left.phase < right.phase;
}

/// An occurrence is admitted only with at least one germ, every germ admitted,
/// and no duplicate germ. A duplicate is refused rather than deduplicated,
/// because repeated testimony is recurrence and the caller must say which it
/// means.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(
    const resonance_occurrence& occurrence) noexcept {
  if (occurrence.germ_count == 0 || occurrence.germ_count > germ_capacity) {
    return false;
  }
  if (occurrence.has_informant && !fiber_law::admitted(occurrence.informant)) {
    return false;
  }
  for (std::uint8_t slot = 0; slot < occurrence.germ_count; ++slot) {
    if (!admitted(occurrence.germs[slot])) {
      return false;
    }
    for (std::uint8_t other = 0; other < slot; ++other) {
      if (equal(key_of(occurrence.germs[slot]), key_of(occurrence.germs[other]))) {
        return false;
      }
    }
  }
  return true;
}

/// Form an inherited informant path. Every adjacent germ transport is exposed as
/// a continuation boundary; no alternate continuation or target is supplied.
[[nodiscard]] HOLONICS_CALLABLE constexpr resonance_occurrence continuation_informant(
    const receiver_fiber_identity& informant,
    std::uint64_t source_order,
    const resonance_germ* germs,
    std::uint8_t count) noexcept {
  resonance_occurrence occurrence{};
  occurrence.informant = informant;
  occurrence.has_informant = true;
  occurrence.source_order = source_order;
  occurrence.origin = occurrence_origin::inherited;
  occurrence.continuation_exposure = true;
  occurrence.path_continuations = true;
  const std::uint8_t admitted_count = count > germ_capacity ? germ_capacity : count;
  for (std::uint8_t slot = 0; slot < admitted_count; ++slot) {
    occurrence.germs[slot] = germs[slot];
  }
  occurrence.germ_count = admitted_count;
  return occurrence;
}

/// A receiver's question. It carries no informant identity: a question is not an
/// informant, and conflating them is how a query becomes fake testimony.
[[nodiscard]] HOLONICS_CALLABLE constexpr resonance_occurrence probe(
    std::uint64_t source_order,
    const resonance_germ* germs,
    std::uint8_t count) noexcept {
  resonance_occurrence occurrence{};
  occurrence.source_order = source_order;
  occurrence.origin = occurrence_origin::receiver_question;
  occurrence.continuation_exposure = true;
  const std::uint8_t admitted_count = count > germ_capacity ? germ_capacity : count;
  for (std::uint8_t slot = 0; slot < admitted_count; ++slot) {
    occurrence.germs[slot] = germs[slot];
  }
  occurrence.germ_count = admitted_count;
  return occurrence;
}

}  // namespace germ_law
}  // namespace holonics::organ
