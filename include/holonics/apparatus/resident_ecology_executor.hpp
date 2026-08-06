#pragma once

#include <cstdint>

#include <holonics/apparatus/exact_executor.hpp>
#include <holonics/organ/incidence_arena.hpp>

namespace holonics::apparatus {

/// The declared aperture of one resident mount. Capacities are **physical
/// testimony, never an admission gate** — exceeding one is a resource
/// obstruction the caller resolves by changing partition or aperture, not by
/// widening a number.
struct resident_mount_request final {
  std::uint32_t sources{};
  std::uint32_t path_length{};
  std::uint32_t state_capacity{};
  std::uint32_t transition_capacity{};
  std::uint32_t occurrence_capacity{};
  std::uint32_t query_paths{};
};

/// What one resident mount returned.
///
/// `resident_octets` is the ecology the apparatus holds. `frame_octets` is what
/// actually crosses into a kernel frame — the two arena values, which are spans
/// and counters and nothing else. **Their ratio is the phase 7 movement 2 grade.**
///
/// `host_replay_work` counts formation steps attributable to the device path. It
/// must be zero: the query laws take the arena by const reference, so a hot
/// device path that replayed the host algorithm would not compile.
struct resident_mount_receipt final {
  executor_status state{executor_status::invalid_aperture};
  std::uint32_t states{};
  std::uint32_t transitions{};
  std::uint32_t occurrences{};
  std::uint32_t ordered{};
  std::uint64_t formation_steps{};
  std::uint64_t lookup_steps{};
  std::uint64_t resident_octets{};
  std::uint64_t frame_octets{};
  std::uint32_t device_queries{};
  std::uint32_t parity_failures{};
  std::uint64_t host_replay_work{};
  bool standing_unchanged{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == executor_status::returned;
  }
  /// The mount holds if the card answered every declared query exactly as the
  /// host does, changed no standing, and replayed no formation.
  [[nodiscard]] constexpr bool holds() const noexcept {
    return returned() && parity_failures == 0 && host_replay_work == 0 &&
        standing_unchanged && device_queries != 0 && ordered == occurrences;
  }
};

/// Form one suffix ecology and its source incidence in resident storage the
/// apparatus owns, then answer a declared query population from the card
/// through spans alone.
[[nodiscard]] resident_mount_receipt mount_resident_ecology(
    resident_mount_request request) noexcept;

/// The germ population of a declared mount. Deterministic and shared by the host
/// formation and the query path, so a parity failure is a real disagreement and
/// never a differently generated material.
///
/// The high term breaks the low term's cycle, so informant paths stay distinct
/// across the whole declared source population instead of repeating every
/// alphabet period — a mount whose paths silently coincide would measure the
/// crossing against a far smaller ecology than it claims.
[[nodiscard]] HOLONICS_CALLABLE constexpr organ::suffix_symbol mount_germ(
    std::uint32_t source,
    std::uint32_t slot) noexcept {
  return organ::suffix_symbol{organ::symbol_kind::germ,
      1U + (((source * 7U) + (slot * 3U) + ((source >> 8U) * 5U)) & 0x3FFU)};
}

}  // namespace holonics::apparatus
