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
/// The Phase 6 grade condition: mounted-only withholds, the cultivated body
/// returns, and a source-detached remount returns a NOVEL product.
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
