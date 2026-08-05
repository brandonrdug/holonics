#pragma once

#include <holonics/event/resident_cultivated_organs.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline bool resident_cultivated_organs::form_cultivation(
    cultivation_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::developmental ||
      !out.inquiry.theory_formed || !codec::render_cultivation(
          cultivation_surface(cards_, out.inquiry), out.passage.formal)) return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit = body_.commit(body_.head(), 0, 0,
      out.inquiry.passage.value(), static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed) return false;
  const checker_outbound_occurrence outbound{body_.head(), exact::word{163'100},
      exact::word{163'101}, exact::word{163'102}, exact::word{163'103},
      exact::word{163'104}, out.inquiry.passage, out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(), outbound};
  pending_live_ = true; out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true; return true;
}

HOLONICS_CALLABLE inline bool resident_cultivated_organs::resume_cultivation(
    const checker_raw_return &raw, cultivation_observation &out) noexcept {
  out.passage.raw = raw; auto *live = pending();
  if (live == nullptr || !live->resumable()) return false;
  const auto expected = live->outbound(); auto &typed = out.passage.typed;
  typed.passage = raw.passage; typed.source = raw.source;
  if (raw.predecessor != expected.predecessor || raw.event != expected.event ||
      raw.port != expected.expected_return_port || raw.lineage.value() != expected.lineage.value() + 1U ||
      raw.passage != expected.passage || raw.source != expected.source) {
    typed.state = checker_return_status::passage_mismatch; return false;
  }
  constexpr char declaration[] = "Soma.Holonics.R31.generated_cultivated_shift_organs";
  constexpr char source[] = "theorem generated_cultivated_shift_organs";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &morphology = out.passage.returned_morphology;
  morphology.mathematical_before = standing_.mathematical_morphology;
  morphology.codec_before = standing_.codec_morphology;
  standing_.mathematical_morphology += accepted ? 32U : 1U;
  standing_.codec_morphology += accepted ? 12U : 1U;
  cultivation_morphology_ += accepted ? 48U : 1U; organ_morphology_ += accepted ? 64U : 0U;
  morphology.commit = body_.commit(expected.predecessor, 0, accepted ? 64U : 1U,
      expected.passage.value(), live->take_continuation()); pending_live_ = false;
  morphology.mathematical_after = standing_.mathematical_morphology;
  morphology.codec_after = standing_.codec_morphology;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    for (std::uint8_t i = 0; i < organ::cultivation_family_count; ++i) {
      organs_[i] = out.inquiry.families[i].candidate;
      organs_[i].identity = exact::word{198'300U + i}; organs_[i].passage = expected.passage;
      organs_[i].returned_event = raw.event; organs_[i].checker_founded = true;
      out.passage.acquired[i] = organs_[i];
    }
    stage_ = stage::cultivated;
  }
  return accepted && morphology.returned_difference_applied;
}

}  // namespace holonics::event
