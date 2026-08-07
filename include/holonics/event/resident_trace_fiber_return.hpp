#pragma once

#include <holonics/event/resident_trace_fiber.hpp>

namespace holonics::event {
namespace trace_fiber_return_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool matches(
    const checker_raw_return &raw,
    const checker_outbound_occurrence &expected) noexcept {
  return raw.predecessor == expected.predecessor && raw.event == expected.event &&
         raw.port == expected.expected_return_port &&
         raw.lineage.value() == expected.lineage.value() + 1U &&
         raw.passage == expected.passage && raw.source == expected.source;
}
} // namespace trace_fiber_return_detail
HOLONICS_CALLABLE inline bool resident_trace_fiber::form_discovery(
    trace_fiber_discovery_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::developmental ||
      !out.inquiry.theory_formed ||
      !codec::render_trace_fiber(trace_fiber_surface(out.inquiry),
                                 out.passage.formal))
    return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit =
      body_.commit(body_.head(), 0, out.inquiry.passage.value(),
                   static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{
      body_.head(),         exact::word{166'100}, exact::word{166'101},
      exact::word{166'102}, exact::word{166'103}, exact::word{166'104},
      out.inquiry.passage,  out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true;
  return true;
}
HOLONICS_CALLABLE inline bool resident_trace_fiber::resume_discovery(
    const checker_raw_return &raw,
    trace_fiber_discovery_observation &out) noexcept {
  out.passage.raw = raw;
  auto *live = pending();
  if (live == nullptr || !live->resumable())
    return false;
  const auto expected = live->outbound();
  auto &typed = out.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (!trace_fiber_return_detail::matches(raw, expected)) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R34.generated_trace_fiber_lifting";
  constexpr char source[] = "theorem generated_trace_fiber_lifting";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source,
                               typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &m = out.passage.returned_morphology;
  m.commit = body_.commit(expected.predecessor, 0,
                          expected.passage.value(), live->take_continuation());
  pending_live_ = false;
  m.returned_difference_applied = accepted &&
      m.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && m.returned_difference_applied) {
    law_.discovery = {exact::word{201'300}, expected.passage, raw.event,
                      out.inquiry.lineage, true};
    out.passage.acquired = law_.discovery;
    for (std::uint8_t target = 0; target < 2; ++target) {
      law_.organs[target] = out.inquiry.organs[target];
      law_.organs[target].identity = exact::word{201'301U + target};
      law_.organs[target].passage = expected.passage;
      law_.organs[target].returned_event = raw.event;
      law_.organs[target].checker_founded = true;
    }
    for (std::uint8_t i = 0; i < 3; ++i)
      law_.triple_count[i] = out.inquiry.triple_count[i];
    law_.group_count = out.inquiry.group_count;
    law_.branch_count = out.inquiry.branch_count;
    law_.two_sheet_count = out.inquiry.two_sheet_count;
    law_.checker_founded = true;
    stage_ = stage::derived;
  }
  return accepted && m.returned_difference_applied;
}
HOLONICS_CALLABLE inline bool resident_trace_fiber::form_heldout(
    heldout_trace_fiber_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::derived ||
      !out.inquiry.theory_formed ||
      !codec::render_heldout_trace_fiber(heldout_trace_fiber_surface(out.inquiry),
                                         out.passage.formal))
    return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit =
      body_.commit(body_.head(), 0, out.inquiry.passage.value(),
                   static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed)
    return false;
  const checker_outbound_occurrence outbound{
      body_.head(),         exact::word{166'110}, exact::word{166'111},
      exact::word{166'112}, exact::word{166'113}, exact::word{166'114},
      out.inquiry.passage,  out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_))
      checker_pending_deed{body_.take_continuation(), outbound};
  pending_live_ = true;
  out.passage.outbound = outbound;
  out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true;
  return true;
}
HOLONICS_CALLABLE inline bool resident_trace_fiber::resume_heldout(
    const checker_raw_return &raw,
    heldout_trace_fiber_observation &out) noexcept {
  out.passage.raw = raw;
  auto *live = pending();
  if (live == nullptr || !live->resumable())
    return false;
  const auto expected = live->outbound();
  auto &typed = out.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  if (!trace_fiber_return_detail::matches(raw, expected)) {
    typed.state = checker_return_status::passage_mismatch;
    return false;
  }
  constexpr char declaration[] =
      "Soma.Holonics.R34.generated_heldout_trace_fiber";
  constexpr char source[] = "theorem generated_heldout_trace_fiber";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source,
                               typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &m = out.passage.returned_morphology;
  m.commit = body_.commit(expected.predecessor, 0,
                          expected.passage.value(), live->take_continuation());
  pending_live_ = false;
  m.returned_difference_applied = accepted &&
      m.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && m.returned_difference_applied) {
    application_ = {exact::word{201'303}, expected.passage, raw.event,
                    out.inquiry.lineage, true};
    stage_ = stage::applied;
  }
  return accepted && m.returned_difference_applied;
}

} // namespace holonics::event
