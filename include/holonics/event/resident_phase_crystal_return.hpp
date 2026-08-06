#pragma once

#include <holonics/event/resident_phase_crystal.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline bool resident_phase_crystal::resume(
    const checker_raw_return& raw, phase_crystal_observation& observation) noexcept {
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
  phase_crystal_checker_detail::normalize(raw, observation.formal, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.returned_morphology;
  morphology.mathematical_before = mathematical_admitted_tally_;
  morphology.codec_before = codec_admitted_tally_;
  mathematical_admitted_tally_ += accepted ? 7U : 1U;
  codec_admitted_tally_ += accepted ? 3U : 2U;
  phase_admitted_tally_ += accepted ? 14U : 1U;
  const std::uint64_t delta = accepted ? 11U : 4U;
  morphology.commit = body_.commit(expected.predecessor, 0, delta,
      expected.passage.value(), pending->take_continuation());
  pending_live_ = false;
  morphology.mathematical_after = mathematical_admitted_tally_;
  morphology.codec_after = codec_admitted_tally_;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  observation.pending_after_return = pending_live_;
  observation.passage_preserved = typed.passage == expected.passage &&
      observation.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    phase_crystal_ = {exact::word{185'300}, expected.passage, raw.event,
        observation.inquiry.theory.lineage, exact::word{delta}, true};
    observation.acquired = phase_crystal_;
  }
  return morphology.returned_difference_applied;
}

HOLONICS_CALLABLE inline phase_crystal_rest_receipt resident_phase_crystal::rest(
    phase_crystal_rest_record& record) noexcept {
  phase_crystal_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted ||
      !geometry_.accepted || !phase_crystal_.accepted || pending_live_) { return receipt; }
  receipt.body = body_.rest(record.body);
  if (!receipt.body.returned) { return receipt; }
  record.first = first_;
  record.second = second_;
  record.geometry = geometry_;
  record.phase_crystal = phase_crystal_;
  record.mathematical_admitted_tally = mathematical_admitted_tally_;
  record.codec_admitted_tally = codec_admitted_tally_;
  record.geometry_admitted_tally = geometry_admitted_tally_;
  record.phase_admitted_tally = phase_admitted_tally_;
  record.integrity = phase_crystal_rest_integrity(record);
  receipt.atlas = phase_crystal_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = first_.accepted && second_.accepted && geometry_.accepted;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

}  // namespace holonics::event
