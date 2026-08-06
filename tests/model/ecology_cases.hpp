#pragma once

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
