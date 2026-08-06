#pragma once

#include <holonics/event/resident_arithmetic_spectral.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline bool resident_arithmetic_spectral::form(
    arithmetic_spectral_observation& observation) noexcept {
  if (!admitted_ || pending_live_ || stage_ != passage_stage::none ||
      !observation.inquiry.theory_formed) { return false; }
  const auto surface = arithmetic_spectral_surface(observation.inquiry);
  if (!codec::render_arithmetic_spectral(surface, observation.passage.formal) ||
      !codec::render_arithmetic_spectral_explanation(surface, observation.passage.conversational)) {
    observation.inquiry.obstruction = organ::arithmetic_spectral_obstruction::render_refused;
    return false;
  }
  auto continuation = body_.take_continuation();
  observation.passage.formation_commit = body_.commit(body_.head(), 0, 47,
      observation.inquiry.theory.passage.value(),
      static_cast<body::linear_continuation&&>(continuation));
  if (observation.passage.formation_commit.state != body::body_change_status::committed) {
    observation.inquiry.obstruction = organ::arithmetic_spectral_obstruction::continuation_refused;
    return false;
  }
  const checker_outbound_occurrence outbound{body_.head(), exact::word{162'500},
      exact::word{162'501}, exact::word{162'502}, exact::word{162'503}, exact::word{162'504},
      observation.inquiry.theory.passage, observation.passage.formal.identity};
  ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(), outbound};
  pending_live_ = true; observation.passage.outbound = outbound;
  observation.passage.checker_stage = checker_stage_status::exact;
  observation.passage.pending_before_process = true; return true;
}

HOLONICS_CALLABLE inline bool resident_arithmetic_spectral::resume(
    const checker_raw_return& raw, arithmetic_spectral_observation& observation) noexcept {
  observation.passage.raw = raw; auto* pending = live_pending();
  if (pending == nullptr || !pending->resumable()) { return false; }
  const auto expected = pending->outbound(); auto& typed = observation.passage.typed;
  typed.passage = raw.passage; typed.source = raw.source;
  const bool lineage_exact = raw.predecessor == expected.predecessor && raw.event == expected.event &&
      raw.port == expected.expected_return_port && raw.lineage.value() == expected.lineage.value() + 1U &&
      raw.passage == expected.passage && raw.source == expected.source;
  if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
  constexpr char declaration[] = "Soma.Holonics.R29.generated_arithmetic_spectral_placement";
  constexpr char source[] = "theorem generated_arithmetic_spectral_placement";
  cm_checker_detail::normalize(raw, observation.passage.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.passage.returned_morphology;
  morphology.mathematical_before = mathematical_admitted_tally_;
  morphology.codec_before = codec_admitted_tally_;
  mathematical_admitted_tally_ += accepted ? 25U : 1U; codec_admitted_tally_ += accepted ? 10U : 2U;
  arithmetic_spectral_admitted_tally_ += accepted ? 47U : 1U;
  const std::uint64_t delta = accepted ? 42U : 4U;
  morphology.commit = body_.commit(expected.predecessor, 0, delta,
      expected.passage.value(), pending->take_continuation()); pending_live_ = false;
  morphology.mathematical_after = mathematical_admitted_tally_;
  morphology.codec_after = codec_admitted_tally_;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  observation.passage.pending_after_return = pending_live_;
  observation.passage.passage_preserved = typed.passage == expected.passage &&
      observation.passage.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    arithmetic_spectral_ = {exact::word{196'300}, expected.passage, raw.event,
        observation.inquiry.theory.lineage, exact::word{delta}, true};
    observation.passage.acquired = arithmetic_spectral_; stage_ = passage_stage::returned;
  }
  return morphology.returned_difference_applied && accepted;
}

}  // namespace holonics::event
