#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/carried_occurrence.hpp>

namespace holonics::structure {

enum class incidence_sign : std::int8_t { negative = -1, positive = 1 };

/// The `I` of the minimum carrier.
///
/// An oriented incidence names one face occurrence of one cell occurrence, with
/// its orientation and its source-local boundary coordinate. **`slot` is a
/// source-local coordinate. It is not chronology, not a global identity, and not
/// an ordering over the population.**
struct oriented_incidence final {
  exact::word cell{};
  exact::word face{};
  incidence_sign sign{incidence_sign::positive};
  std::uint16_t slot{};
};

/// A bounded oriented boundary: the faces of one cell, retained in slot order as
/// the source declared them.
template<std::size_t Capacity>
struct oriented_boundary final {
  static_assert(Capacity > 0);
  oriented_incidence faces[Capacity]{};
  std::uint16_t used{};
};

namespace incidence_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(
    const oriented_incidence& value) noexcept {
  return value.cell.value() != 0 && value.face.value() != 0 &&
      value.cell != value.face;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr incidence_sign opposed(
    incidence_sign sign) noexcept {
  return sign == incidence_sign::positive ? incidence_sign::negative
                                          : incidence_sign::positive;
}

/// **The cancellation law.** Opposed coefficients cancel only when actual gluing
/// makes them coefficients of the SAME face occurrence. Equal but unglued face
/// occurrences are different basis elements and cannot cancel, however equal
/// their payloads or their boundaries.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool cancels(
    const oriented_incidence& left,
    const oriented_incidence& right) noexcept {
  return admitted(left) && admitted(right) && left.cell == right.cell &&
      left.face == right.face && left.sign == opposed(right.sign);
}

/// Two incidences over face occurrences that are merely equal-valued are
/// distinct basis elements. Exposed so a caller cannot reach cancellation by
/// comparing payloads.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool distinct_basis(
    const oriented_incidence& left,
    const oriented_incidence& right) noexcept {
  return admitted(left) && admitted(right) && left.face != right.face;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_append(
    oriented_boundary<Capacity>& boundary,
    const oriented_incidence& value) noexcept {
  if (!admitted(value) || boundary.used >= Capacity) {
    return false;
  }
  boundary.faces[boundary.used] = value;
  boundary.used = static_cast<std::uint16_t>(boundary.used + 1U);
  return true;
}

/// `boundary(boundary) = 0` over the retained population: every face of a face
/// appears with both orientations and cancels against the same face occurrence.
/// A cell whose second boundary does not close is refused, never repaired.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool second_boundary_closes(
    const oriented_boundary<Capacity>& lower) noexcept {
  for (std::uint16_t index = 0; index < lower.used; ++index) {
    bool matched = false;
    for (std::uint16_t other = 0; other < lower.used; ++other) {
      if (other != index && cancels(lower.faces[index], lower.faces[other])) {
        matched = true;
        break;
      }
    }
    if (!matched) {
      return false;
    }
  }
  return true;
}

}  // namespace incidence_law
}  // namespace holonics::structure
