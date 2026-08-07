#pragma once

#include <holonics/event/resident_expression_geometry.hpp>

namespace holonics::event {
HOLONICS_CALLABLE inline bool resident_expression_geometry::form(
    expression_geometry_observation& observation) noexcept {
  if (!admitted_ || pending_live_ || stage_ != passage_stage::none ||
      !observation.inquiry.theory_formed || !observation.changed_sensitive) { return false; }
  const auto surface = expression_geometry_surface(
      observation.inquiry, observation.changed, observation.changed_sensitive);
  if (!codec::render_expression_geometry(surface, observation.passage.formal) ||
      !codec::render_expression_geometry_explanation(surface, observation.passage.conversational)) {
    observation.inquiry.obstruction = organ::expression_geometry_obstruction::render_refused;
    return false;
  }
  auto continuation = body_.take_continuation();
  observation.passage.formation_commit = body_.commit(body_.head(), 0,
      observation.inquiry.theory.passage.value(),
      static_cast<body::linear_continuation&&>(continuation));
  if (observation.passage.formation_commit.state != body::body_change_status::committed) {
    observation.inquiry.obstruction = organ::expression_geometry_obstruction::continuation_refused;
    return false;
  }
  const checker_outbound_occurrence outbound{body_.head(), exact::word{161'400},
      exact::word{161'401}, exact::word{161'402}, exact::word{161'403}, exact::word{161'404},
      observation.inquiry.theory.passage, observation.passage.formal.identity};
  ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(), outbound};
  pending_live_ = true; observation.passage.outbound = outbound;
  observation.passage.checker_stage = checker_stage_status::exact;
  observation.passage.pending_before_process = true; return true;
}

HOLONICS_CALLABLE inline bool resident_expression_geometry::resume(
    const checker_raw_return& raw, expression_geometry_observation& observation) noexcept {
  observation.passage.raw = raw; auto* pending = live_pending();
  if (pending == nullptr || !pending->resumable()) { return false; }
  const auto expected = pending->outbound(); auto& typed = observation.passage.typed;
  typed.passage = raw.passage; typed.source = raw.source;
  const bool lineage_exact = raw.predecessor == expected.predecessor && raw.event == expected.event &&
      raw.port == expected.expected_return_port && raw.lineage.value() == expected.lineage.value() + 1U &&
      raw.passage == expected.passage && raw.source == expected.source;
  if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
  constexpr char declaration[] = "Soma.Holonics.R27.generated_expression_geometry";
  constexpr char source[] = "theorem generated_expression_geometry";
  cm_checker_detail::normalize(raw, observation.passage.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.passage.returned_morphology;  morphology.commit = body_.commit(expected.predecessor, 0,
      expected.passage.value(), pending->take_continuation()); pending_live_ = false;
  morphology.returned_difference_applied = accepted &&
      morphology.commit.state == body::body_change_status::committed;
  observation.passage.pending_after_return = pending_live_;
  observation.passage.passage_preserved = typed.passage == expected.passage &&
      observation.passage.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    expression_geometry_ = {exact::word{194'300}, expected.passage, raw.event,
        observation.inquiry.theory.lineage, true};
    observation.passage.acquired = expression_geometry_; stage_ = passage_stage::returned;
  }
  return morphology.returned_difference_applied && accepted;
}

}  // namespace holonics::event
