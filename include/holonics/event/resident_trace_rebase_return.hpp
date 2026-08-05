#pragma once

#include <holonics/event/resident_trace_rebase.hpp>

namespace holonics::event {
namespace trace_rebase_return_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool matches(
    const checker_raw_return &raw,
    const checker_outbound_occurrence &expected) noexcept {
  return raw.predecessor == expected.predecessor && raw.event == expected.event &&
         raw.port == expected.expected_return_port &&
         raw.lineage.value() == expected.lineage.value() + 1U &&
         raw.passage == expected.passage && raw.source == expected.source;
}
} // namespace trace_rebase_return_detail
HOLONICS_CALLABLE inline bool resident_trace_rebase::form_discovery_surface(
    trace_rebase_discovery_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::developmental ||
      !out.inquiry.theory_formed)
    return false;
  return codec::render_trace_rebase(trace_rebase_surface(out.inquiry),
                                    out.passage.formal);
}
HOLONICS_CALLABLE inline bool resident_trace_rebase::form_discovery(
    trace_rebase_discovery_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::developmental ||
      !out.inquiry.theory_formed || out.passage.formal.byte_count == 0)
    return false;
  if (!codec::trace_rebase_render_detail::render_trace_rebase_witnesses(
          trace_rebase_witness_surface(out.inquiry), out.passage.formal))
    return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit = body_.commit(
      body_.head(), 0, 0, out.inquiry.passage.value(),
      static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{
      body_.head(), exact::word{167'100}, exact::word{167'101},
      exact::word{167'102}, exact::word{167'103}, exact::word{167'104},
      out.inquiry.passage, out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true;
  return true;
}
HOLONICS_CALLABLE inline bool resident_trace_rebase::resume_discovery(
    const checker_raw_return &raw,
    trace_rebase_discovery_observation &out) noexcept {
  out.passage.raw = raw;
  auto *live = pending();
  if (live == nullptr || !live->resumable())
    return false;
  const auto expected = live->outbound();
  auto &typed = out.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (!trace_rebase_return_detail::matches(raw, expected)) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R35.generated_trace_character_rebases";
  constexpr char source[] = "theorem generated_trace_character_rebases";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source,
                               typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &m = out.passage.returned_morphology;
  m.mathematical_before =
      standing_.standing.standing.standing.standing.mathematical_morphology;
  m.codec_before = standing_.standing.standing.standing.standing.codec_morphology;
  standing_.standing.standing.standing.standing.mathematical_morphology +=
      accepted ? 48U : 1U;
  standing_.standing.standing.standing.standing.codec_morphology +=
      accepted ? 24U : 1U;
  rebase_morphology_ += accepted ? 80U : 1U;
  differential_morphology_ += accepted ? 56U : 0U;
  deck_morphology_ += accepted ? 24U : 0U;
  m.commit = body_.commit(expected.predecessor, 0, accepted ? 96U : 1U,
                          expected.passage.value(), live->take_continuation());
  pending_live_ = false;
  m.mathematical_after =
      standing_.standing.standing.standing.standing.mathematical_morphology;
  m.codec_after = standing_.standing.standing.standing.standing.codec_morphology;
  m.returned_difference_applied =
      m.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && m.returned_difference_applied) {
    law_.discovery = {exact::word{202'300}, expected.passage, raw.event,
                      out.inquiry.lineage, exact::word{48}, true};
    out.passage.acquired = law_.discovery;
    for (std::uint8_t i = 0; i < organ::trace_rebase_move_count; ++i) {
      law_.maps[i] = out.inquiry.maps[i];
      law_.maps[i].identity = exact::word{202'301U + i};
      law_.maps[i].passage = expected.passage;
      law_.maps[i].returned_event = raw.event;
      law_.maps[i].checker_founded = true;
      law_.transitions[i] = out.inquiry.transitions[i];
    }
    law_.tangent = {exact::word{202'306}, expected.passage, raw.event,
                    out.inquiry.lineage, exact::word{56}, true};
    law_.deck.return_receipt = {
        exact::word{202'307}, expected.passage, raw.event,
        out.inquiry.lineage, exact::word{24}, true};
    for (std::uint8_t i = 0; i < organ::trace_rebase_coordinate_count; ++i) {
      law_.deck.vector[i] = out.inquiry.witnesses[3].vector[i];
      law_.deck.image[i] = out.inquiry.witnesses[3].image[i];
    }
    law_.deck.eigenvalue = out.inquiry.witnesses[3].eigenvalue;
    law_.deck.primitive = out.inquiry.witnesses[3].found;
    law_.checker_founded = true;
    stage_ = stage::derived;
  }
  return accepted && m.returned_difference_applied;
}
HOLONICS_CALLABLE inline bool resident_trace_rebase::form_heldout(
    heldout_trace_rebase_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::derived ||
      !out.inquiry.theory_formed ||
      !codec::render_heldout_trace_rebase(
          heldout_trace_rebase_surface(out.inquiry), out.passage.formal))
    return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit = body_.commit(
      body_.head(), 0, 0, out.inquiry.passage.value(),
      static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{
      body_.head(), exact::word{167'110}, exact::word{167'111},
      exact::word{167'112}, exact::word{167'113}, exact::word{167'114},
      out.inquiry.passage, out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true;
  return true;
}
HOLONICS_CALLABLE inline bool resident_trace_rebase::resume_heldout(
    const checker_raw_return &raw,
    heldout_trace_rebase_observation &out) noexcept {
  out.passage.raw = raw;
  auto *live = pending();
  if (live == nullptr || !live->resumable())
    return false;
  const auto expected = live->outbound();
  auto &typed = out.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (!trace_rebase_return_detail::matches(raw, expected)) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R35.generated_heldout_trace_rebase";
  constexpr char source[] = "theorem generated_heldout_trace_rebase";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source,
                               typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &m = out.passage.returned_morphology;
  m.mathematical_before =
      standing_.standing.standing.standing.standing.mathematical_morphology;
  m.codec_before = standing_.standing.standing.standing.standing.codec_morphology;
  standing_.standing.standing.standing.standing.mathematical_morphology +=
      accepted ? 16U : 1U;
  standing_.standing.standing.standing.standing.codec_morphology +=
      accepted ? 8U : 1U;
  path_morphology_ += accepted ? 32U : 1U;
  m.commit = body_.commit(expected.predecessor, 0, accepted ? 32U : 1U,
                          expected.passage.value(), live->take_continuation());
  pending_live_ = false;
  m.mathematical_after =
      standing_.standing.standing.standing.standing.mathematical_morphology;
  m.codec_after = standing_.standing.standing.standing.standing.codec_morphology;
  m.returned_difference_applied =
      m.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && m.returned_difference_applied) {
    application_ = {exact::word{202'308}, expected.passage, raw.event,
                    out.inquiry.lineage, exact::word{32}, true};
    stage_ = stage::applied;
  }
  return accepted && m.returned_difference_applied;
}

} // namespace holonics::event
