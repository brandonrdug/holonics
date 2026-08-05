#pragma once

#include <holonics/event/resident_characteristic_hypergeometry.hpp>

namespace holonics::event {
namespace characteristic_return_detail {
HOLONICS_CALLABLE inline bool
matches(const checker_raw_return &raw,
        const checker_outbound_occurrence &expected) noexcept {
  return raw.predecessor == expected.predecessor &&
         raw.event == expected.event &&
         raw.port == expected.expected_return_port &&
         raw.lineage.value() == expected.lineage.value() + 1U &&
         raw.passage == expected.passage && raw.source == expected.source;
}
} // namespace characteristic_return_detail
HOLONICS_CALLABLE inline bool
resident_characteristic_hypergeometry::form_discovery(
    characteristic_discovery_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::developmental ||
      !out.inquiry.theory_formed ||
      !codec::render_characteristic_hypergeometry(
          characteristic_surface(out.inquiry), out.passage.formal))
    return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit =
      body_.commit(body_.head(), 0, 0, out.inquiry.passage.value(),
                   static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{
      body_.head(),         exact::word{165'100},       exact::word{165'101},
      exact::word{165'102}, exact::word{165'103},       exact::word{165'104},
      out.inquiry.passage,  out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true;
  return true;
}
HOLONICS_CALLABLE inline bool
resident_characteristic_hypergeometry::resume_discovery(
    const checker_raw_return &raw,
    characteristic_discovery_observation &out) noexcept {
  out.passage.raw = raw;
  auto *live = pending();
  if (live == nullptr || !live->resumable())
    return false;
  const auto expected = live->outbound();
  auto &typed = out.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (!characteristic_return_detail::matches(raw, expected)) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R33.generated_characteristic_hypergeometry";
  constexpr char source[] = "theorem generated_characteristic_hypergeometry";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source,
                               typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &m = out.passage.returned_morphology;
  m.mathematical_before = standing_.standing.standing.mathematical_morphology;
  m.codec_before = standing_.standing.standing.codec_morphology;
  standing_.standing.standing.mathematical_morphology += accepted ? 36U : 1U;
  standing_.standing.standing.codec_morphology += accepted ? 16U : 1U;
  characteristic_morphology_ += accepted ? 64U : 1U;
  trace_organ_morphology_ += accepted ? 32U : 0U;
  m.commit = body_.commit(expected.predecessor, 0, accepted ? 72U : 1U,
                          expected.passage.value(), live->take_continuation());
  pending_live_ = false;
  m.mathematical_after = standing_.standing.standing.mathematical_morphology;
  m.codec_after = standing_.standing.standing.codec_morphology;
  m.returned_difference_applied =
      m.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && m.returned_difference_applied) {
    law_.discovery = {exact::word{200'300}, expected.passage, raw.event,
                      out.inquiry.lineage,  exact::word{40},  true};
    out.passage.acquired = law_.discovery;
    law_.organ = out.inquiry.organ;
    law_.organ.identity = exact::word{200'301};
    law_.organ.passage = expected.passage;
    law_.organ.returned_event = raw.event;
    law_.organ.checker_founded = true;
    law_.group_count = out.inquiry.group_count;
    for (std::uint8_t i = 0; i < 3; ++i) {
      law_.pair_count[i] = out.inquiry.pair_count[i];
      law_.closed_strata[i] = out.inquiry.closed_strata[i];
    }
    law_.checker_founded = true;
    stage_ = stage::derived;
  }
  return accepted && m.returned_difference_applied;
}
HOLONICS_CALLABLE inline bool
resident_characteristic_hypergeometry::form_heldout(
    heldout_characteristic_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::derived ||
      !out.inquiry.theory_formed ||
      !codec::render_heldout_characteristic(
          heldout_characteristic_surface(out.inquiry), out.passage.formal))
    return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit =
      body_.commit(body_.head(), 0, 0, out.inquiry.passage.value(),
                   static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{
      body_.head(),         exact::word{165'110},       exact::word{165'111},
      exact::word{165'112}, exact::word{165'113},       exact::word{165'114},
      out.inquiry.passage,  out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true;
  return true;
}
HOLONICS_CALLABLE inline bool
resident_characteristic_hypergeometry::resume_heldout(
    const checker_raw_return &raw,
    heldout_characteristic_observation &out) noexcept {
  out.passage.raw = raw;
  auto *live = pending();
  if (live == nullptr || !live->resumable())
    return false;
  const auto expected = live->outbound();
  auto &typed = out.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (!characteristic_return_detail::matches(raw, expected)) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R33.generated_heldout_characteristic_transport";
  constexpr char source[] =
      "theorem generated_heldout_characteristic_transport";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source,
                               typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &m = out.passage.returned_morphology;
  m.mathematical_before = standing_.standing.standing.mathematical_morphology;
  m.codec_before = standing_.standing.standing.codec_morphology;
  standing_.standing.standing.mathematical_morphology += accepted ? 12U : 1U;
  standing_.standing.standing.codec_morphology += accepted ? 8U : 1U;
  transport_morphology_ += accepted ? 24U : 1U;
  m.commit = body_.commit(expected.predecessor, 0, accepted ? 24U : 1U,
                          expected.passage.value(), live->take_continuation());
  pending_live_ = false;
  m.mathematical_after = standing_.standing.standing.mathematical_morphology;
  m.codec_after = standing_.standing.standing.codec_morphology;
  m.returned_difference_applied =
      m.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && m.returned_difference_applied) {
    application_ = {exact::word{200'302}, expected.passage, raw.event,
                    out.inquiry.lineage,  exact::word{24},  true};
    stage_ = stage::applied;
  }
  return accepted && m.returned_difference_applied;
}

} // namespace holonics::event
