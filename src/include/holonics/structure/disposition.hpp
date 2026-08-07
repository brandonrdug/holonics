#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/chi_pair.hpp>

namespace holonics::structure {

/// The returned disposition of a transport attempt.
///
/// **`open` is a first-class standing state, not an error and not a Boolean
/// false.** A noncommuting comparison stands OPEN carrying the exact attempted
/// routes and their receiver-relative residual. It does **not** negate either
/// path, divide an antecedent, choose a correction, found a higher relation, or
/// blacklist a future route. A genuinely later current may supply a filler, a
/// rebase, a bypass, a contextual distinction, or another OPEN.
enum class disposition : std::uint8_t { ride, found, open, holonomy };

/// The retained body of an OPEN. It holds the complete pair, never a code.
struct open_standing final {
  chi_pair attempted{};
  chi_projection_receipt refusal{};
  exact::word receiver{};
};

/// A three-way order with an OPEN. Even comparison has an OPEN: two exact
/// carriers may be incomparable in a declared receiver without either being
/// greater.
enum class ordering : std::uint8_t { less, equal, greater, open };

struct returned_disposition final {
  disposition state{disposition::open};
  open_standing standing{};
  exact::word winding{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool concluded() const noexcept {
    return state == disposition::ride || state == disposition::found;
  }
};

namespace disposition_law {

/// A transport that closed through standing terrain. Cheap because the terrain
/// already paid.
[[nodiscard]] HOLONICS_CALLABLE constexpr returned_disposition ride() noexcept {
  returned_disposition value{};
  value.state = disposition::ride;
  return value;
}

/// A founding deposits exactly one integer winding quantum. It pays curvature.
/// A founding with no winding is malformed and is refused here rather than
/// silently admitted.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_found(
    exact::word winding,
    returned_disposition& value) noexcept {
  if (winding.value() == 0) {
    return false;
  }
  value = returned_disposition{};
  value.state = disposition::found;
  value.winding = winding;
  return true;
}

/// Stand OPEN, retaining the complete attempted pair and the reason the
/// projection was unavailable.
[[nodiscard]] HOLONICS_CALLABLE constexpr returned_disposition stand_open(
    const chi_pair& attempted,
    chi_projection_receipt refusal,
    exact::word receiver) noexcept {
  returned_disposition value{};
  value.state = disposition::open;
  value.standing = open_standing{attempted, refusal, receiver};
  return value;
}

/// A closed route that returned a changed frame.
[[nodiscard]] HOLONICS_CALLABLE constexpr returned_disposition holonomy(
    const chi_pair& returned_word) noexcept {
  returned_disposition value{};
  value.state = disposition::holonomy;
  value.standing.attempted = returned_word;
  return value;
}

/// **The refusal law of OPEN.** An OPEN may not be converted into a conclusion
/// by any later reading of the same routes. Only genuinely new current may
/// change it, and that arrives as a fresh attempt, never as a reinterpretation.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool may_conclude_from(
    const returned_disposition& value) noexcept {
  return value.state != disposition::open;
}

/// An OPEN retains everything: nothing about the attempted pair is discarded,
/// so a later declared chart can project what this receiver could not.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool retains_complete_pair(
    const returned_disposition& value) noexcept {
  return value.state != disposition::open ||
      chi_law::admitted(value.standing.attempted);
}

}  // namespace disposition_law
}  // namespace holonics::structure
