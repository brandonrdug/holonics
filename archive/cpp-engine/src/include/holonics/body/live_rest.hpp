#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/live_machine.hpp>

namespace holonics::body {

inline constexpr std::uint64_t live_rest_magic = 0x484F'4C4F'4E52'4553ULL;
inline constexpr std::uint64_t live_rest_layout_version = 1;

/// Exact native rest.
///
/// The rest carries standing, lineages, head, and root. It carries **no
/// aperture**: the aperture is a rebuildable substrate cache, so its absence
/// from the wire is the proof that it is not causal.
///
/// Delivery order is gauge: the same occurrences in a different administrative
/// order produce the same rest words. An unknown magic or version **fails
/// closed** — there is no route back to a rejected body.
struct live_rest_header final {
  std::uint64_t magic{live_rest_magic};
  std::uint64_t version{live_rest_layout_version};
  std::uint64_t head{};
  std::uint64_t root{};
  std::uint64_t standing_nodes{};
  std::uint64_t lineages{};
  std::uint64_t integrity{};
};

namespace rest_law {

/// A carried, order-independent digest over the retained words. It locates and
/// compares; it never establishes identity, and a match is not a proof that two
/// bodies are the same causal diagram.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t fold(
    std::uint64_t accumulated,
    std::uint64_t word) noexcept {
  const std::uint64_t mixed = accumulated ^ (word + 0x9E37'79B9'7F4A'7C15ULL +
      (accumulated << 6U) + (accumulated >> 2U));
  return mixed;
}

template<class Form, std::size_t StandingCapacity, std::size_t LineageCapacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr live_rest_header header_of(
    const live_machine<Form, StandingCapacity, LineageCapacity>& machine) noexcept {
  live_rest_header header{};
  header.head = machine.head().value();
  header.root = machine.root();
  header.standing_nodes = machine.standing().used();
  header.lineages = machine.lineage_count();
  std::uint64_t integrity = 0;
  integrity = fold(integrity, header.magic);
  integrity = fold(integrity, header.version);
  integrity = fold(integrity, header.head);
  integrity = fold(integrity, header.root);
  integrity = fold(integrity, header.standing_nodes);
  integrity = fold(integrity, header.lineages);
  for (std::uint32_t slot = 0; slot < machine.lineage_count(); ++slot) {
    const live_lineage* carried = machine.lineage(slot);
    integrity = fold(integrity, carried->channel.value());
    integrity = fold(integrity, carried->groove.value());
    integrity = fold(integrity, carried->winding.value());
    integrity = fold(integrity, carried->tip);
  }
  for (std::uint32_t node = 0; node < machine.standing().used(); ++node) {
    const auto* cell = machine.standing().at(node);
    integrity = fold(integrity, cell->cell.address.chart);
    integrity = fold(integrity, cell->cell.address.grip);
    integrity = fold(integrity, cell->lower);
    integrity = fold(integrity, cell->higher);
  }
  header.integrity = integrity;
  return header;
}

/// Admission at the mouth. Old and unknown standing **fails closed**: there is
/// no decoder, adapter, dual schema, or replay path for a rejected wire.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool admits(
    const live_rest_header& header) noexcept {
  return header.magic == live_rest_magic &&
      header.version == live_rest_layout_version;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool intact(
    const live_rest_header& header,
    const live_rest_header& recomputed) noexcept {
  return admits(header) && header.integrity == recomputed.integrity &&
      header.head == recomputed.head && header.root == recomputed.root &&
      header.standing_nodes == recomputed.standing_nodes &&
      header.lineages == recomputed.lineages;
}

/// The aperture is absent from the wire by construction. This predicate is the
/// standing check that it stayed absent.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool aperture_absent_from_rest(
    const live_rest_header& header) noexcept {
  static_cast<void>(header);
  return sizeof(live_rest_header) ==
      sizeof(std::uint64_t) * 7U;
}

}  // namespace rest_law
}  // namespace holonics::body
