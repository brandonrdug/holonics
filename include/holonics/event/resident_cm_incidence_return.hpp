#pragma once

#include <holonics/event/resident_cm_incidence.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline bool resident_cm_incidence::form(
    const organ::cm_incidence_question& question,
    cm_incidence_observation& observation) noexcept {
  if (!admitted_ || pending_live_ || stage_ != passage_stage::none) { return false; }
  organ::cm_incidence_detail::form_candidates(observation.inquiry);
  organ::cm_incidence_detail::close_cm_incidence(foundation_, question, observation.inquiry);
  const auto& inquiry = observation.inquiry;
  codec::cm_incidence_surface surface{};
  surface.passage = inquiry.theory.passage;
  surface.periodic_factor_count = inquiry.periodic.factor_count;
  surface.window_factor_count = inquiry.window.factor_count;
  surface.periodic_edges = inquiry.periodic.edge_count;
  surface.window_edges = inquiry.window.edge_count;
  surface.lost_edges = inquiry.projection.lost_count;
  surface.unit_pairs = inquiry.projection.unit_pair_count;
  surface.projection_loss = inquiry.projection.projection_loss;
  surface.norm_one = inquiry.theory.norm_one;
  surface.incidence_agreement = inquiry.theory.incidence_agreement;
  surface.characteristic_transport = inquiry.theory.characteristic_transport;
  surface.aperture_scattering = inquiry.theory.aperture_scattering;
  surface.alternatives_retained = inquiry.theory.alternatives_retained;
  for (std::size_t slot = 0; slot < organ::cm_translation_capacity; ++slot) {
    surface.direction_population[slot] = inquiry.projection.direction_population[slot];
    for (std::size_t coefficient = 0; coefficient < organ::cm_degree_capacity; ++coefficient) {
      surface.translations[slot].coefficients[coefficient] =
          inquiry.translations[slot].value.coefficients[coefficient];
    }
  }
  for (std::size_t slot = 0; slot < organ::cm_characteristic_capacity; ++slot) {
    surface.periodic_characteristic[slot] = inquiry.periodic.characteristic[slot];
    surface.window_characteristic[slot] = inquiry.window.characteristic[slot];
  }
  for (std::size_t slot = 0; slot < organ::cm_factor_capacity; ++slot) {
    surface.periodic_factors[slot].degree = inquiry.periodic.factors[slot].degree;
    surface.periodic_factors[slot].multiplicity =
        inquiry.periodic.factors[slot].multiplicity;
    surface.periodic_factors[slot].exact = inquiry.periodic.factors[slot].exact;
    surface.window_factors[slot].degree = inquiry.window.factors[slot].degree;
    surface.window_factors[slot].multiplicity = inquiry.window.factors[slot].multiplicity;
    surface.window_factors[slot].exact = inquiry.window.factors[slot].exact;
    for (std::size_t coefficient = 0; coefficient < organ::cm_factor_capacity; ++coefficient) {
      surface.periodic_factors[slot].coefficients[coefficient] =
          inquiry.periodic.factors[slot].coefficients[coefficient];
      surface.window_factors[slot].coefficients[coefficient] =
          inquiry.window.factors[slot].coefficients[coefficient];
    }
  }
  if (!inquiry.theory_formed ||
      !codec::render_cm_incidence(surface, observation.passage.formal) ||
      !codec::render_cm_explanation(surface, observation.passage.conversational)) {
    observation.inquiry.obstruction = organ::cm_obstruction::render_refused; return false;
  }
  auto continuation = body_.take_continuation();
  observation.passage.formation_commit = body_.commit(body_.head(), 0, 15,
      inquiry.theory.passage.value(), static_cast<body::linear_continuation&&>(continuation));
  if (observation.passage.formation_commit.state != body::body_change_status::committed) {
    observation.inquiry.obstruction = organ::cm_obstruction::continuation_refused; return false;
  }
  const checker_outbound_occurrence outbound{body_.head(), exact::word{160'900},
      exact::word{160'901}, exact::word{160'902}, exact::word{160'903},
      exact::word{160'904}, inquiry.theory.passage, observation.passage.formal.identity};
  ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(), outbound};
  pending_live_ = true;
  observation.passage.outbound = outbound;
  observation.passage.checker_stage = checker_stage_status::exact;
  observation.passage.pending_before_process = true;
  return true;
}

HOLONICS_CALLABLE inline bool resident_cm_incidence::resume(
    const checker_raw_return& raw, cm_incidence_observation& observation) noexcept {
  observation.passage.raw = raw;
  auto* pending = live_pending();
  if (pending == nullptr || !pending->resumable()) { return false; }
  const auto expected = pending->outbound();
  auto& typed = observation.passage.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  const bool lineage_exact = raw.predecessor == expected.predecessor &&
      raw.event == expected.event && raw.port == expected.expected_return_port &&
      raw.lineage.value() == expected.lineage.value() + 1U &&
      raw.passage == expected.passage && raw.source == expected.source;
  if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
  constexpr char declaration[] =
      "Soma.Holonics.R22.generated_cm_characteristic_transport";
  constexpr char source[] = "theorem generated_cm_characteristic_transport";
  cm_checker_detail::normalize(raw, observation.passage.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.passage.returned_morphology;
  morphology.mathematical_before = mathematical_admitted_tally_;
  morphology.codec_before = codec_admitted_tally_;
  mathematical_admitted_tally_ += accepted ? 10U : 1U;
  codec_admitted_tally_ += accepted ? 4U : 2U;
  cm_incidence_admitted_tally_ += accepted ? 17U : 1U;
  const std::uint64_t delta = accepted ? 16U : 4U;
  morphology.commit = body_.commit(expected.predecessor, 0, delta,
      expected.passage.value(), pending->take_continuation());
  pending_live_ = false;
  morphology.mathematical_after = mathematical_admitted_tally_;
  morphology.codec_after = codec_admitted_tally_;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  observation.passage.pending_after_return = pending_live_;
  observation.passage.passage_preserved = typed.passage == expected.passage &&
      observation.passage.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    cm_incidence_ = {exact::word{189'300}, expected.passage, raw.event,
        observation.inquiry.theory.lineage, exact::word{delta}, true};
    observation.passage.acquired = cm_incidence_;
    stage_ = passage_stage::returned;
  }
  return morphology.returned_difference_applied && accepted;
}

HOLONICS_CALLABLE inline cm_incidence_rest_receipt resident_cm_incidence::rest(
    cm_incidence_rest_record& record) noexcept {
  cm_incidence_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted || !geometry_.accepted ||
      !phase_crystal_.accepted || !characteristic_.accepted || !regular_singular_.accepted ||
      !code_reconstruction_.accepted || !moment_reconstruction_.accepted ||
      !cm_incidence_.accepted || pending_live_ || stage_ != passage_stage::returned) {
    return receipt;
  }
  receipt.body = body_.rest(record.body);
  if (!receipt.body.returned) { return receipt; }
  record.first = first_;
  record.second = second_;
  record.geometry = geometry_;
  record.phase_crystal = phase_crystal_;
  record.characteristic = characteristic_;
  record.regular_singular = regular_singular_;
  record.code_reconstruction = code_reconstruction_;
  record.moment_reconstruction = moment_reconstruction_;
  record.cm_incidence = cm_incidence_;
  record.mathematical_admitted_tally = mathematical_admitted_tally_;
  record.codec_admitted_tally = codec_admitted_tally_;
  record.geometry_admitted_tally = geometry_admitted_tally_;
  record.phase_admitted_tally = phase_admitted_tally_;
  record.characteristic_admitted_tally = characteristic_admitted_tally_;
  record.regular_singular_admitted_tally = regular_singular_admitted_tally_;
  record.blind_reconstruction_admitted_tally = blind_reconstruction_admitted_tally_;
  record.cm_incidence_admitted_tally = cm_incidence_admitted_tally_;
  record.integrity = cm_incidence_rest_integrity(record);
  receipt.theory = cm_incidence_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = first_.accepted && second_.accepted && geometry_.accepted &&
      phase_crystal_.accepted && characteristic_.accepted && regular_singular_.accepted &&
      code_reconstruction_.accepted && moment_reconstruction_.accepted;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

}  // namespace holonics::event
