#pragma once

#include <holonics/event/resident_cultivated_organs.hpp>

namespace holonics::event {
HOLONICS_CALLABLE inline bool resident_cultivated_organs::form_application(
    cultivated_application_observation &out) noexcept {
  if (!admitted_ || pending_live_ || stage_ != stage::cultivated ||
      !out.inquiry.theory_formed ||
      !codec::render_cultivated_application(
          cultivated_application_surface(out.inquiry, organs_), out.passage.formal)) return false;
  auto continuation = body_.take_continuation();
  out.passage.formation_commit = body_.commit(body_.head(), 0,
      out.inquiry.passage.value(), static_cast<body::linear_continuation &&>(continuation));
  if (out.passage.formation_commit.state != body::body_change_status::committed) return false;
  const checker_outbound_occurrence outbound{body_.head(), exact::word{163'110},
      exact::word{163'111}, exact::word{163'112}, exact::word{163'113},
      exact::word{163'114}, out.inquiry.passage, out.passage.formal.identity};
  ::new (static_cast<void *>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(), outbound}; pending_live_ = true;
  out.passage.outbound = outbound; out.passage.checker_stage = checker_stage_status::exact;
  out.passage.pending_before_process = true; return true;
}

HOLONICS_CALLABLE inline bool resident_cultivated_organs::resume_application(
    const checker_raw_return &raw, cultivated_application_observation &out) noexcept {
  out.passage.raw = raw; auto *live = pending();
  if (live == nullptr || !live->resumable()) return false;
  const auto expected = live->outbound(); auto &typed = out.passage.typed;
  typed.passage = raw.passage; typed.source = raw.source;
  if (raw.predecessor != expected.predecessor || raw.event != expected.event ||
      raw.port != expected.expected_return_port || raw.lineage.value() != expected.lineage.value() + 1U ||
      raw.passage != expected.passage || raw.source != expected.source) {
    typed.state = checker_return_status::passage_mismatch; return false;
  }
  constexpr char declaration[] = "Soma.Holonics.R31.generated_cultivated_organs_transport";
  constexpr char source[] = "theorem generated_cultivated_organs_transport";
  cm_checker_detail::normalize(raw, out.passage.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto &morphology = out.passage.returned_morphology;
  morphology.commit = body_.commit(expected.predecessor, 0,
      expected.passage.value(), live->take_continuation()); pending_live_ = false;
  morphology.returned_difference_applied = accepted &&
      morphology.commit.state == body::body_change_status::committed;
  out.passage.pending_after_return = pending_live_;
  out.passage.passage_preserved = raw.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    application_ = {exact::word{198'304}, expected.passage, raw.event,
        out.inquiry.lineage, true};
    stage_ = stage::applied;
  }
  return accepted && morphology.returned_difference_applied;
}

}  // namespace holonics::event
