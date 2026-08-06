#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::structure {

/// The `O` of the minimum carrier.
///
/// An occurrence is an ACTUAL k-dimensional event, not a value. Two occurrences
/// may carry identical payloads and identical boundaries and still be two
/// members of the population. **Multiplicity is represented by distinct
/// occurrence identities, never by a set of values and never by a numeric
/// coefficient.**
///
/// Grade, grain, stage, and chart are independent typings. They are given
/// distinct types here so that no assignment between them can compile: they are
/// not synonyms, and conflating them was the historical error this carrier
/// exists to prevent.
struct occurrence_grade final {
  std::uint8_t value{};
  friend HOLONICS_CALLABLE constexpr bool operator==(
      occurrence_grade, occurrence_grade) noexcept = default;
};

struct occurrence_grain final {
  std::uint8_t value{};
  friend HOLONICS_CALLABLE constexpr bool operator==(
      occurrence_grain, occurrence_grain) noexcept = default;
};

struct occurrence_stage final {
  std::uint32_t value{};
  friend HOLONICS_CALLABLE constexpr bool operator==(
      occurrence_stage, occurrence_stage) noexcept = default;
};

struct occurrence_chart final {
  std::uint32_t value{};
  friend HOLONICS_CALLABLE constexpr bool operator==(
      occurrence_chart, occurrence_chart) noexcept = default;
};

template<class Payload>
struct carried_occurrence final {
  exact::word identity{};
  occurrence_grade grade{};
  occurrence_grain grain{};
  occurrence_stage stage{};
  occurrence_chart chart{};
  Payload payload{};
};

namespace occurrence_law {

/// Occurrence identity is the ONLY equality. Equal payloads do not identify.
template<class Payload>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_occurrence(
    const carried_occurrence<Payload>& left,
    const carried_occurrence<Payload>& right) noexcept {
  return left.identity == right.identity && left.identity.value() != 0;
}

/// True exactly when two members carry the same payload while remaining two
/// distinct occurrences. This is the case a value-set or coefficient
/// representation destroys, so it is exposed as a first-class predicate.
template<class Payload, class PayloadEqual>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool plural_at_equal_payload(
    const carried_occurrence<Payload>& left,
    const carried_occurrence<Payload>& right,
    PayloadEqual equal) noexcept {
  return !same_occurrence(left, right) && equal(left.payload, right.payload);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(exact::word identity) noexcept {
  return identity.value() != 0;
}

/// Two occurrences may share a grade and differ in grain, or share a grain and
/// differ in chart. Nothing derives one typing from another.
template<class Payload>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_typing(
    const carried_occurrence<Payload>& left,
    const carried_occurrence<Payload>& right) noexcept {
  return left.grade == right.grade && left.grain == right.grain &&
      left.stage == right.stage && left.chart == right.chart;
}

}  // namespace occurrence_law
}  // namespace holonics::structure
