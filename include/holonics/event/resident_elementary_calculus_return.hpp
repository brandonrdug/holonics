#pragma once

#include <holonics/event/resident_elementary_calculus.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline bool resident_elementary_calculus::form_calculus(
    elementary_calculus_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::developmental ||
      !out.inquiry.theory_formed || !codec::render_elementary_calculus(
          elementary_surface(cards_,out.inquiry),out.passage.formal)) return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit = body_.commit(body_.head(),0,0,out.inquiry.passage.value(),
      static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed) return false;
  const checker_outbound_occurrence outbound{body_.head(),exact::word{164'100},
      exact::word{164'101},exact::word{164'102},exact::word{164'103},exact::word{164'104},
      out.inquiry.passage,out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(),outbound}; pending_live_ = true; out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true; return true;
}

HOLONICS_CALLABLE inline bool resident_elementary_calculus::resume_calculus(
    const checker_raw_return &raw, elementary_calculus_observation &out) noexcept {
  out.passage.raw = raw; auto *live = pending(); if (live == nullptr || !live->resumable()) return false;
  const auto expected = live->outbound(); auto &typed = out.passage.typed;
  typed.passage = raw.passage; typed.source = raw.source;
  if (raw.predecessor != expected.predecessor || raw.event != expected.event ||
      raw.port != expected.expected_return_port || raw.lineage.value() != expected.lineage.value()+1U ||
      raw.passage != expected.passage || raw.source != expected.source) {
    typed.state = checker_return_status::passage_mismatch; return false;
  }
  constexpr char declaration[] = "Soma.Holonics.R32.generated_elementary_causal_calculus";
  constexpr char source[] = "theorem generated_elementary_causal_calculus";
  cm_checker_detail::normalize(raw,out.passage.formal,declaration,source,typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &morphology = out.passage.returned_morphology;
  morphology.mathematical_before = standing_.standing.mathematical_morphology;
  morphology.codec_before = standing_.standing.codec_morphology;
  standing_.standing.mathematical_morphology += accepted ? 40U : 1U;
  standing_.standing.codec_morphology += accepted ? 16U : 1U;
  calculus_morphology_ += accepted ? 64U : 1U;
  self_organ_morphology_ += accepted ? 32U : 0U;
  morphology.commit = body_.commit(expected.predecessor,0,accepted ? 80U : 1U,
      expected.passage.value(),live->take_continuation()); pending_live_ = false;
  morphology.mathematical_after = standing_.standing.mathematical_morphology;
  morphology.codec_after = standing_.standing.codec_morphology;
  morphology.returned_difference_applied = morphology.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_; out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    constexpr std::uint8_t deltas[6]{16,16,12,12,12,12};
    for (std::uint8_t i = 0; i < 6; ++i) {
      laws_.fibers[i] = {exact::word{199'300U+i},expected.passage,raw.event,
          exact::word{out.inquiry.lineage.value()+i},exact::word{deltas[i]},true};
      out.passage.acquired[i] = laws_.fibers[i];
    }
    laws_.self_organ = out.inquiry.self_organ.organ;
    laws_.self_organ.identity = exact::word{199'305}; laws_.self_organ.passage = expected.passage;
    laws_.self_organ.returned_event = raw.event; laws_.self_organ.checker_founded = true;
    laws_.occurrence_mask = out.inquiry.occurrence.selected_mask;
    laws_.boundary_exact = out.inquiry.occurrence.boundary_squared_zero;
    for (std::uint8_t i = 0; i < 5; ++i)
      laws_.composition_codes[i] = static_cast<std::uint8_t>(out.inquiry.composition.signatures[i].code);
    laws_.coarse_fibers = out.inquiry.receiver.coarse_fibers;
    laws_.fine_fibers = out.inquiry.receiver.fine_fibers;
    laws_.strict_witnesses = out.inquiry.receiver.coarse_strict_witnesses;
    laws_.receiver_reopens = !out.inquiry.receiver.strict_factors_coarse &&
        out.inquiry.receiver.strict_factors_fine;
    laws_.path_residual = out.inquiry.chart.residual; laws_.closed_word = out.inquiry.chart.closed_word;
    laws_.curved = out.inquiry.chart.curved; laws_.conduct_code = out.inquiry.conduct.selected_code;
    for (std::uint8_t i = 0; i < 7; ++i)
      laws_.conduct_conditions[i] = out.inquiry.conduct.selected_conditions[i];
    laws_.conduct_exact = out.inquiry.conduct.theory_formed; laws_.checker_founded = true;
    stage_ = stage::derived;
  }
  return accepted && morphology.returned_difference_applied;
}

HOLONICS_CALLABLE inline bool resident_elementary_calculus::form_heldout(
    heldout_holonomy_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::derived || !out.inquiry.theory_formed ||
      !codec::render_heldout_holonomy(heldout_surface(out.inquiry,laws_.self_organ),
                                     out.passage.formal)) return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit = body_.commit(body_.head(),0,0,out.inquiry.passage.value(),
      static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed) return false;
  const checker_outbound_occurrence outbound{body_.head(),exact::word{164'110},
      exact::word{164'111},exact::word{164'112},exact::word{164'113},exact::word{164'114},
      out.inquiry.passage,out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(),outbound}; pending_live_ = true; out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true; return true;
}

HOLONICS_CALLABLE inline bool resident_elementary_calculus::resume_heldout(
    const checker_raw_return &raw, heldout_holonomy_observation &out) noexcept {
  out.passage.raw = raw; auto *live = pending(); if (live == nullptr || !live->resumable()) return false;
  const auto expected = live->outbound(); auto &typed = out.passage.typed;
  typed.passage = raw.passage; typed.source = raw.source;
  if (raw.predecessor != expected.predecessor || raw.event != expected.event ||
      raw.port != expected.expected_return_port || raw.lineage.value() != expected.lineage.value()+1U ||
      raw.passage != expected.passage || raw.source != expected.source) {
    typed.state = checker_return_status::passage_mismatch; return false;
  }
  constexpr char declaration[] = "Soma.Holonics.R32.generated_heldout_holonomy_transport";
  constexpr char source[] = "theorem generated_heldout_holonomy_transport";
  cm_checker_detail::normalize(raw,out.passage.formal,declaration,source,typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &morphology = out.passage.returned_morphology;
  morphology.mathematical_before = standing_.standing.mathematical_morphology;
  morphology.codec_before = standing_.standing.codec_morphology;
  standing_.standing.mathematical_morphology += accepted ? 12U : 1U;
  standing_.standing.codec_morphology += accepted ? 8U : 1U;
  derivation_morphology_ += accepted ? 24U : 1U;
  morphology.commit = body_.commit(expected.predecessor,0,accepted ? 24U : 1U,
      expected.passage.value(),live->take_continuation()); pending_live_ = false;
  morphology.mathematical_after = standing_.standing.mathematical_morphology;
  morphology.codec_after = standing_.standing.codec_morphology;
  morphology.returned_difference_applied = morphology.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_; out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    application_ = {exact::word{199'306},expected.passage,raw.event,out.inquiry.lineage,
        exact::word{24},true}; stage_ = stage::applied;
  }
  return accepted && morphology.returned_difference_applied;
}

}  // namespace holonics::event
