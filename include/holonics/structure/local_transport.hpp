#pragma once

#include <cstdint>

#include <holonics/structure/carried_occurrence.hpp>

namespace holonics::structure {

/// The `T` of the minimum carrier.
///
/// A local transport carries the relation an occurrence holds from its source to
/// its target. **It is not assumed invertible, linear, metric, probabilistic, or
/// scalar.** Every one of those is a property a source may DECLARE, and every
/// consumer that needs one must ask for it and be refused when it is absent.
enum class transport_property : std::uint8_t {
  invertible = 0,
  additive = 1,
  linear = 2,
  metric = 3,
  ordered = 4,
  projective_chart = 5
};

struct transport_declaration final {
  std::uint8_t declared{};
};

namespace transport_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t bit(
    transport_property property) noexcept {
  return static_cast<std::uint8_t>(1U << static_cast<std::uint8_t>(property));
}

[[nodiscard]] HOLONICS_CALLABLE constexpr transport_declaration declare(
    transport_declaration current,
    transport_property property) noexcept {
  return transport_declaration{
      static_cast<std::uint8_t>(current.declared | bit(property))};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool carries(
    transport_declaration declaration,
    transport_property property) noexcept {
  return (declaration.declared & bit(property)) != 0U;
}

}  // namespace transport_law

/// One transport occurrence: a source, a target, the relation's own identity,
/// and the properties its source declared. The relation body itself is opaque
/// here; this owner carries its typing and its lineage, not its arithmetic.
struct local_transport final {
  exact::word identity{};
  exact::word source{};
  exact::word target{};
  transport_declaration declaration{};
};

namespace transport_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(
    const local_transport& value) noexcept {
  return value.identity.value() != 0 && value.source.value() != 0 &&
      value.target.value() != 0;
}

/// Serial composition. The composite inherits only the properties BOTH factors
/// declared: composing an invertible transport with a non-invertible one does
/// not produce an invertible composite, and nothing here assumes otherwise.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_compose(
    const local_transport& first,
    const local_transport& second,
    exact::word composite_identity,
    local_transport& composite) noexcept {
  if (!admitted(first) || !admitted(second) || first.target != second.source ||
      composite_identity.value() == 0) {
    return false;
  }
  composite = local_transport{
      composite_identity, first.source, second.target,
      transport_declaration{static_cast<std::uint8_t>(
          first.declaration.declared & second.declaration.declared)}};
  return true;
}

/// Two transports are parallel when they share a source and a target. Parallel
/// transports are the input to `Chi`; they are not thereby equal, and no
/// comparison of them is available until a chart is declared.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool parallel(
    const local_transport& left,
    const local_transport& right) noexcept {
  return admitted(left) && admitted(right) && left.source == right.source &&
      left.target == right.target;
}

}  // namespace transport_law
}  // namespace holonics::structure
