#pragma once

#include <cstdint>

namespace holonics::tests {

/// Phase 6.2: suffix automaton state bound, boundary separation, recurrence
/// multiplicity, and the linear source-incidence attribution.
[[nodiscard]] bool suffix_laws_hold();
/// Phase 6.3: recurrence-gated activation, transactional staging, and an
/// ablation that removes structure rather than a counter.
[[nodiscard]] bool training_laws_hold();
/// Phase 6.5: parented codec revision resuming the same continuation.
[[nodiscard]] bool reflective_laws_hold();

}  // namespace holonics::tests
namespace holonics::tests {
/// Phase 6.4, 6.6-6.9: surface scales, relational conduct, the typed mouth,
/// exterior-checker crossing, and research fronts.
[[nodiscard]] bool surface_laws_hold();
[[nodiscard]] bool relational_laws_hold();
[[nodiscard]] bool mouth_laws_hold();
[[nodiscard]] bool formal_laws_hold();
[[nodiscard]] bool research_laws_hold();
}  // namespace holonics::tests
namespace holonics::tests {
/// WITHDRAWN 2026-08-06 (CUT 5). Retained as a type so the conformance report
/// still compiles; it returns nothing and grades nothing.
struct ablation_return final {
  std::uint64_t mounted_only{};
  bool mounted_withheld{};
  std::uint64_t cultivated{};
  std::uint64_t novel_after_departure{};
  bool developmental_passages_retained{};
  bool ablated_stops_conducting{};
  bool holds{};
};
[[nodiscard]] ablation_return cultivation_ablation();
}  // namespace holonics::tests

namespace holonics::tests {
/// phase 7 movement 1: the cost law of the suffix ecology, measured across a quadrupled
/// aperture. Formation and lookup must stay linear; the returned work figures
/// are the artifact and the ratio bound is the falsifier.
struct cost_return final {
  std::uint32_t small_symbols{};
  std::uint32_t large_symbols{};
  std::uint32_t small_states{};
  std::uint32_t large_states{};
  std::uint64_t small_formation{};
  std::uint64_t large_formation{};
  std::uint64_t small_lookup{};
  std::uint64_t large_lookup{};
  bool formation_linear{};
  bool lookup_linear{};
  bool holds{};
};
[[nodiscard]] cost_return suffix_cost_law();
}  // namespace holonics::tests
