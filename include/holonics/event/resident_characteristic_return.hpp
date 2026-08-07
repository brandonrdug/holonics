#pragma once

#include <holonics/event/resident_characteristic.hpp>

namespace holonics::event {
HOLONICS_CALLABLE inline bool resident_characteristic::resume(
    const checker_raw_return& raw, characteristic_observation& observation) noexcept {
  observation.raw = raw;
  auto* pending = live_pending();
  if (pending == nullptr || !pending->resumable()) { return false; }
  const auto expected = pending->outbound();
  auto& typed = observation.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  const bool lineage_exact = raw.predecessor == expected.predecessor &&
      raw.event == expected.event && raw.port == expected.expected_return_port &&
      raw.lineage.value() == expected.lineage.value() + 1U &&
      raw.passage == expected.passage && raw.source == expected.source;
  if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
  characteristic_checker_detail::normalize(raw, observation.formal, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.returned_morphology;
  morphology.commit = body_.commit(expected.predecessor, 0,
      expected.passage.value(), pending->take_continuation());
  pending_live_ = false;
  morphology.returned_difference_applied = accepted &&
      morphology.commit.state == body::body_change_status::committed;
  observation.pending_after_return = pending_live_;
  observation.passage_preserved = typed.passage == expected.passage &&
      observation.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    characteristic_ = {exact::word{186'300}, expected.passage, raw.event,
        observation.inquiry.theory.lineage, true};
    observation.acquired = characteristic_;
  }
  return morphology.returned_difference_applied;
}

HOLONICS_CALLABLE inline characteristic_rest_receipt resident_characteristic::rest(
    characteristic_rest_record& record) noexcept {
  characteristic_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted || !geometry_.accepted ||
      !phase_crystal_.accepted || !characteristic_.accepted || pending_live_) { return receipt; }
  receipt.body = body_.rest(record.body);
  if (!receipt.body.returned) { return receipt; }
  record.first = first_;
  record.second = second_;
  record.geometry = geometry_;
  record.phase_crystal = phase_crystal_;
  record.characteristic = characteristic_;
  record.integrity = characteristic_rest_integrity(record);
  receipt.theory = characteristic_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = first_.accepted && second_.accepted &&
      geometry_.accepted && phase_crystal_.accepted;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

}  // namespace holonics::event
