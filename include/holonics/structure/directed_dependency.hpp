#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/structure/oriented_incidence.hpp>

namespace holonics::structure {

/// The `D` of the minimum carrier.
///
/// Directed dependency is **a different relation from boundary incidence** and
/// is carried in a different type so the two can never be substituted. An
/// incidence says what boundary an occurrence has. A dependency says what caused
/// what.
///
/// Hardware simultaneity is neither necessary nor sufficient for a dependency
/// edge, and nothing here derives one from call order, key order, worker lane,
/// or serialized position.
struct directed_dependency final {
  exact::word antecedent{};
  exact::word consequent{};
};

/// A dependency cut is a finite, explicitly bounded population of edges over
/// which acyclicity is asserted and checked. Acyclicity is a property of the
/// declared cut, never a global claim about the ecology.
template<std::size_t Capacity>
struct dependency_cut final {
  static_assert(Capacity > 0);
  directed_dependency edges[Capacity]{};
  std::uint16_t used{};
};

namespace dependency_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(
    const directed_dependency& value) noexcept {
  return value.antecedent.value() != 0 && value.consequent.value() != 0 &&
      value.antecedent != value.consequent;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool try_append(
    dependency_cut<Capacity>& cut,
    const directed_dependency& edge) noexcept {
  if (!admitted(edge) || cut.used >= Capacity) {
    return false;
  }
  cut.edges[cut.used] = edge;
  cut.used = static_cast<std::uint16_t>(cut.used + 1U);
  return true;
}

/// Is `target` reachable from `origin` inside the declared cut? Bounded by the
/// edge count, so a cyclic cut terminates instead of diverging.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool reaches(
    const dependency_cut<Capacity>& cut,
    exact::word origin,
    exact::word target) noexcept {
  exact::word frontier[Capacity]{};
  std::uint16_t frontier_used = 0;
  frontier[frontier_used++] = origin;
  for (std::uint16_t step = 0; step <= cut.used; ++step) {
    const std::uint16_t before = frontier_used;
    for (std::uint16_t edge = 0; edge < cut.used; ++edge) {
      bool antecedent_present = false;
      bool consequent_present = false;
      for (std::uint16_t slot = 0; slot < frontier_used; ++slot) {
        antecedent_present =
            antecedent_present || frontier[slot] == cut.edges[edge].antecedent;
        consequent_present =
            consequent_present || frontier[slot] == cut.edges[edge].consequent;
      }
      if (antecedent_present && !consequent_present && frontier_used < Capacity) {
        frontier[frontier_used++] = cut.edges[edge].consequent;
        if (cut.edges[edge].consequent == target) {
          return true;
        }
      }
    }
    if (frontier_used == before) {
      return false;
    }
  }
  return false;
}

/// Acyclic at this cut: no edge's consequent reaches its own antecedent.
template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool acyclic_at_cut(
    const dependency_cut<Capacity>& cut) noexcept {
  for (std::uint16_t edge = 0; edge < cut.used; ++edge) {
    if (reaches(cut, cut.edges[edge].consequent, cut.edges[edge].antecedent)) {
      return false;
    }
  }
  return true;
}

/// A dependency edge and an incidence edge over the same two occurrences remain
/// two separate relations. This predicate exists so a caller that wants to know
/// whether both hold must ask for both, and can never obtain one from the other.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool coincides_with_incidence(
    const directed_dependency& dependency,
    const oriented_incidence& incidence) noexcept {
  return incidence_law::admitted(incidence) && admitted(dependency) &&
      dependency.antecedent == incidence.face &&
      dependency.consequent == incidence.cell;
}

}  // namespace dependency_law
}  // namespace holonics::structure
