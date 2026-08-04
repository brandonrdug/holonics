#pragma once

#include <holonics/event/theorem_production_rest.hpp>

namespace holonics::event {

struct returned_fiber_exclusion_receipt final {
  exact::word excluded_fiber{};
  exact::word excluded_delta{};
  exact::word head_before{};
  exact::word head_after{};
  std::uint64_t body_morphology_before{};
  std::uint64_t body_morphology_after{};
  std::uint64_t mathematical_before{};
  std::uint64_t mathematical_after{};
  std::uint64_t codec_before{};
  std::uint64_t codec_after{};
  bool original_integrity_exact{};
  bool projected_integrity_exact{};
  bool exact{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr returned_fiber_exclusion_receipt
exclude_returned_theorem_fiber(const theorem_production_rest_record& original,
    theorem_production_rest_record& projected) noexcept {
  returned_fiber_exclusion_receipt receipt{};
  receipt.excluded_fiber = original.acquired.identity;
  receipt.excluded_delta = original.acquired.morphology_delta;
  receipt.head_before = exact::word{original.body.head};
  receipt.body_morphology_before = original.body.regions[0].morphology;
  receipt.mathematical_before = original.mathematical_morphology;
  receipt.codec_before = original.codec_morphology;
  receipt.original_integrity_exact =
      original.integrity == theorem_production_rest_integrity(original);
  if (!receipt.original_integrity_exact || !original.acquired.accepted ||
      original.acquired.morphology_delta != exact::word{5} || original.body.head == 0 ||
      original.body.next_head == 0 || original.body.continuation == 0 ||
      original.body.next_continuation == 0 || original.body.lineage == 0 ||
      original.body.regions[0].morphology < 5 || original.mathematical_morphology < 3 ||
      original.codec_morphology < 2) { return receipt; }
  projected.body.head = original.body.head - 1U;
  projected.body.next_head = original.body.next_head - 1U;
  projected.body.continuation = original.body.continuation - 1U;
  projected.body.next_continuation = original.body.next_continuation - 1U;
  projected.body.lineage = original.body.lineage - 1U;
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    projected.body.regions[slot] = original.body.regions[slot];
  }
  projected.body.regions[0].morphology -= 5U;
  projected.body.integrity = body::rest_integrity(projected.body);
  projected.mathematical_morphology = original.mathematical_morphology - 3U;
  projected.codec_morphology = original.codec_morphology - 2U;
  projected.integrity = theorem_production_rest_integrity(projected);
  receipt.head_after = exact::word{projected.body.head};
  receipt.body_morphology_after = projected.body.regions[0].morphology;
  receipt.mathematical_after = projected.mathematical_morphology;
  receipt.codec_after = projected.codec_morphology;
  receipt.projected_integrity_exact =
      projected.integrity == theorem_production_rest_integrity(projected);
  receipt.exact = receipt.projected_integrity_exact &&
      receipt.body_morphology_before - receipt.body_morphology_after == 5U &&
      receipt.mathematical_before - receipt.mathematical_after == 3U &&
      receipt.codec_before - receipt.codec_after == 2U;
  return receipt;
}

}  // namespace holonics::event
