#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/event/formal_production.hpp>
#include <holonics/event/relational_surface.hpp>

namespace holonics::event {

/// A leader: a question-born exploratory front carrying its origin and the
/// boundary it reached.
struct research_leader final {
  std::uint64_t identity{};
  std::uint64_t question{};
  std::uint64_t reached_face{};
  bool bridge{};
  bool closed{};
};

inline constexpr std::size_t leader_capacity = 32;

/// A world-contact front.
///
/// A front is received as **one co-present validated antichain**, not as a
/// sequence. Arrival order inside a front is apparatus, and admitting a front
/// member by member would let call order manufacture chronology.
struct contact_front final {
  research_leader leaders[leader_capacity]{};
  std::uint8_t used{};
  bool validated{};
};

/// Why a research passage rested.
///
/// Rest is **no novel source occurrence and no unvisited caused bridge region**.
/// It is not a reflection count: stopping after a fixed number of rounds would
/// be the controller's budget, not the body's completion.
enum class research_rest : std::uint8_t {
  rested,
  novel_source_remains,
  bridge_region_unvisited
};

namespace research_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_admit(
    contact_front& front,
    const research_leader& leader) noexcept {
  if (front.used >= leader_capacity || leader.identity == 0) {
    return false;
  }
  for (std::uint8_t slot = 0; slot < front.used; ++slot) {
    if (front.leaders[slot].identity == leader.identity) {
      return false;
    }
  }
  front.leaders[front.used] = leader;
  front.used = static_cast<std::uint8_t>(front.used + 1U);
  return true;
}

/// A front crosses only as a whole, and only once validated.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool may_cross(
    const contact_front& front) noexcept {
  return front.validated && front.used != 0;
}

/// **Bridge leaders are emitted by still-open currents from the faces they
/// actually reached.** A closed current emits none, and no leader is invented
/// for a face nothing reached.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t bridge_leaders_owed(
    const contact_front& front) noexcept {
  std::uint8_t owed = 0;
  for (std::uint8_t slot = 0; slot < front.used; ++slot) {
    if (!front.leaders[slot].closed && front.leaders[slot].reached_face != 0) {
      owed = static_cast<std::uint8_t>(owed + 1U);
    }
  }
  return owed;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr research_rest rest_state(
    std::uint32_t novel_source_occurrences,
    std::uint32_t unvisited_bridge_regions) noexcept {
  if (novel_source_occurrences != 0) {
    return research_rest::novel_source_remains;
  }
  if (unvisited_bridge_regions != 0) {
    return research_rest::bridge_region_unvisited;
  }
  return research_rest::rested;
}

/// **Causal exclusion, not a lexical filter.** A grading transcript is excluded
/// by its source identity so a rerun cannot inherit its own recorded answer as
/// testimony. Excluding by spelling would leave the same material reachable
/// under another name.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool source_admitted(
    std::uint64_t source_identity,
    const std::uint64_t* excluded,
    std::uint32_t excluded_count) noexcept {
  for (std::uint32_t slot = 0; slot < excluded_count; ++slot) {
    if (excluded[slot] == source_identity) {
      return false;
    }
  }
  return source_identity != 0;
}

}  // namespace research_law
}  // namespace holonics::event
