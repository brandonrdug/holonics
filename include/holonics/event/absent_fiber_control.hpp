#pragma once

#include <holonics/event/theorem_production_rest.hpp>

namespace holonics::event {

/// **A control, not an ablation.**
///
/// This projects a rest record whose acquired returned fiber is *absent*, so a
/// dependent theorem formed against it must refuse. That refusal is real and
/// worth observing: it shows the dependent passage needs the fiber's identity.
///
/// It is **not** an exact ablation and must never be reported as one. An
/// ablation removes a returned fiber from a conditioned body and observes the
/// later conduct disappear. Nothing here conditions a body, and nothing here
/// removes structure from one: the projection simply withholds the identity.
///
/// The predecessor's own tallies are copied through untouched. The removed
/// version of this law decremented them by hardcoded constants and called the
/// difference a morphology change; that is the mechanism the Phase 0 regrade
/// excised, and it does not return here.
struct absent_fiber_control_receipt final {
  exact::word withheld_fiber{};
  bool original_integrity_exact{};
  bool projected_integrity_exact{};
  bool exact{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr absent_fiber_control_receipt
project_without_returned_fiber(
    const theorem_production_rest_record& original,
    theorem_production_rest_record& projected) noexcept {
  absent_fiber_control_receipt receipt{};
  receipt.withheld_fiber = original.acquired.identity;
  receipt.original_integrity_exact =
      original.integrity == theorem_production_rest_integrity(original);
  if (!receipt.original_integrity_exact || !original.acquired.accepted ||
      original.body.head == 0 || original.body.next_head == 0 ||
      original.body.continuation == 0 || original.body.next_continuation == 0 ||
      original.body.lineage == 0) {
    return receipt;
  }
  projected = original;
  projected.acquired = {};
  projected.integrity = theorem_production_rest_integrity(projected);
  receipt.projected_integrity_exact =
      projected.integrity == theorem_production_rest_integrity(projected);
  receipt.exact = receipt.projected_integrity_exact &&
      projected.acquired.identity.value() == 0 &&
      projected.body.head == original.body.head &&
      projected.mathematical_admitted_tally == original.mathematical_admitted_tally &&
      projected.codec_admitted_tally == original.codec_admitted_tally;
  return receipt;
}

}  // namespace holonics::event
