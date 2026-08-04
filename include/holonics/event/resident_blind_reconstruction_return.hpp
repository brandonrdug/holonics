#pragma once

#include <holonics/event/resident_blind_reconstruction.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline bool resident_blind_reconstruction::resume_code(
    const checker_raw_return& raw, blind_reconstruction_observation& observation) noexcept {
  observation.code.raw = raw;
  auto* pending = live_pending();
  if (pending == nullptr || !pending->resumable() || pending_kind_ != passage_kind::code) {
    return false;
  }
  const auto expected = pending->outbound();
  auto& typed = observation.code.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  const bool lineage_exact = raw.predecessor == expected.predecessor &&
      raw.event == expected.event && raw.port == expected.expected_return_port &&
      raw.lineage.value() == expected.lineage.value() + 1U &&
      raw.passage == expected.passage && raw.source == expected.source;
  if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
  constexpr char declaration[] =
      "Soma.Holonics.R21.Code.generated_tensor_jacobi_eigenvector";
  constexpr char source[] = "theorem generated_tensor_jacobi_eigenvector";
  blind_checker_detail::normalize(raw, observation.code.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.code.returned_morphology;
  morphology.mathematical_before = mathematical_morphology_;
  morphology.codec_before = codec_morphology_;
  mathematical_morphology_ += accepted ? 7U : 1U;
  codec_morphology_ += accepted ? 3U : 2U;
  blind_reconstruction_morphology_ += accepted ? 11U : 1U;
  const std::uint64_t delta = accepted ? 12U : 4U;
  morphology.commit = body_.commit(expected.predecessor, 0, delta,
      expected.passage.value(), pending->take_continuation());
  pending_live_ = false;
  pending_kind_ = passage_kind::none;
  morphology.mathematical_after = mathematical_morphology_;
  morphology.codec_after = codec_morphology_;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  observation.code.pending_after_return = pending_live_;
  observation.code.passage_preserved = typed.passage == expected.passage &&
      observation.code.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    code_reconstruction_ = {exact::word{188'300}, expected.passage, raw.event,
        exact::word{observation.inquiry.theory.lineage.value() + foundation_.code.lineage.value()},
        exact::word{delta}, true};
    observation.code.acquired = code_reconstruction_;
    stage_ = passage_stage::code_returned;
  }
  return morphology.returned_difference_applied && accepted;
}

HOLONICS_CALLABLE inline bool resident_blind_reconstruction::form_moment(
    blind_reconstruction_observation& observation) noexcept {
  if (!admitted_ || pending_live_ || stage_ != passage_stage::code_returned ||
      !code_reconstruction_.accepted) { return false; }
  const auto& plan = observation.inquiry.theory;
  const codec::blind_reconstruction_surface explanation_surface{plan.moment_passage,
      foundation_.moments.lineage, plan.moment_pencil, plan.moment_pencil,
      plan.separability_boundary, plan.alternatives_retained, plan.source_separated};
  codec::blind_moment_surface surface{};
  const auto& first = observation.inquiry.moments[0];
  surface.passage = plan.moment_passage;
  surface.determinant = first.hankel_determinant;
  surface.discriminant = first.discriminant;
  surface.degree = first.degree;
  surface.root_count = first.root_count;
  surface.incidence = plan.moment_pencil;
  surface.characteristic = plan.moment_pencil;
  surface.obstruction = plan.separability_boundary;
  surface.alternatives = plan.alternatives_retained;
  surface.source_separated = plan.source_separated;
  for (std::size_t row = 0; row < codec::blind_moment_degree_capacity; ++row) {
    surface.roots[row] = first.roots[row];
    for (std::size_t column = 0; column < codec::blind_moment_degree_capacity; ++column) {
      surface.hankel[row][column] = first.hankel[row][column];
      surface.shifted[row][column] = first.shifted[row][column];
      surface.collision[row][column] = observation.inquiry.moments[3].hankel[row][column];
    }
  }
  for (std::size_t slot = 0; slot < codec::blind_polynomial_capacity; ++slot) {
    surface.polynomial[slot] = first.newton[slot];
  }
  if (!codec::render_blind_moment(surface, observation.moment.formal) ||
      !codec::render_blind_moment_explanation(
          explanation_surface, observation.moment.conversational)) {
    observation.inquiry.obstruction = organ::blind_obstruction::render_refused; return false;
  }
  auto continuation = body_.take_continuation();
  observation.moment.formation_commit = body_.commit(body_.head(), 0, 13,
      plan.moment_passage.value(), static_cast<body::linear_continuation&&>(continuation));
  if (observation.moment.formation_commit.state != body::body_change_status::committed) {
    observation.inquiry.obstruction = organ::blind_obstruction::continuation_refused; return false;
  }
  const checker_outbound_occurrence outbound{body_.head(), exact::word{160'810},
      exact::word{160'811}, exact::word{160'812}, exact::word{160'813},
      exact::word{160'814}, plan.moment_passage, observation.moment.formal.identity};
  ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(), outbound};
  pending_live_ = true;
  pending_kind_ = passage_kind::moment;
  observation.moment.outbound = outbound;
  observation.moment.checker_stage = checker_stage_status::exact;
  observation.moment.pending_before_process = true;
  return true;
}

HOLONICS_CALLABLE inline bool resident_blind_reconstruction::resume_moment(
    const checker_raw_return& raw, blind_reconstruction_observation& observation) noexcept {
  observation.moment.raw = raw;
  auto* pending = live_pending();
  if (pending == nullptr || !pending->resumable() || pending_kind_ != passage_kind::moment) {
    return false;
  }
  const auto expected = pending->outbound();
  auto& typed = observation.moment.typed;
  typed.passage = raw.passage;
  typed.source = raw.source;
  const bool lineage_exact = raw.predecessor == expected.predecessor &&
      raw.event == expected.event && raw.port == expected.expected_return_port &&
      raw.lineage.value() == expected.lineage.value() + 1U &&
      raw.passage == expected.passage && raw.source == expected.source;
  if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
  constexpr char declaration[] =
      "Soma.Holonics.R21.Moment.generated_hankel_pencil";
  constexpr char source[] = "theorem generated_hankel_pencil";
  blind_checker_detail::normalize(raw, observation.moment.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.moment.returned_morphology;
  morphology.mathematical_before = mathematical_morphology_;
  morphology.codec_before = codec_morphology_;
  mathematical_morphology_ += accepted ? 8U : 1U;
  codec_morphology_ += accepted ? 3U : 2U;
  blind_reconstruction_morphology_ += accepted ? 13U : 1U;
  const std::uint64_t delta = accepted ? 14U : 4U;
  morphology.commit = body_.commit(expected.predecessor, 0, delta,
      expected.passage.value(), pending->take_continuation());
  pending_live_ = false;
  pending_kind_ = passage_kind::none;
  morphology.mathematical_after = mathematical_morphology_;
  morphology.codec_after = codec_morphology_;
  morphology.returned_difference_applied =
      morphology.commit.state == body::body_change_status::committed;
  observation.moment.pending_after_return = pending_live_;
  observation.moment.passage_preserved = typed.passage == expected.passage &&
      observation.moment.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    moment_reconstruction_ = {exact::word{188'301}, expected.passage, raw.event,
        exact::word{observation.inquiry.theory.lineage.value() + foundation_.moments.lineage.value()},
        exact::word{delta}, true};
    observation.moment.acquired = moment_reconstruction_;
    stage_ = passage_stage::moment_returned;
  }
  return morphology.returned_difference_applied && accepted;
}

HOLONICS_CALLABLE inline blind_reconstruction_rest_receipt
resident_blind_reconstruction::rest(blind_reconstruction_rest_record& record) noexcept {
  blind_reconstruction_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted || !geometry_.accepted ||
      !phase_crystal_.accepted || !characteristic_.accepted || !regular_singular_.accepted ||
      !code_reconstruction_.accepted || !moment_reconstruction_.accepted || pending_live_ ||
      stage_ != passage_stage::moment_returned) { return receipt; }
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
  record.mathematical_morphology = mathematical_morphology_;
  record.codec_morphology = codec_morphology_;
  record.geometry_morphology = geometry_morphology_;
  record.phase_morphology = phase_morphology_;
  record.characteristic_morphology = characteristic_morphology_;
  record.regular_singular_morphology = regular_singular_morphology_;
  record.blind_reconstruction_morphology = blind_reconstruction_morphology_;
  record.integrity = blind_reconstruction_rest_integrity(record);
  receipt.code_theory = code_reconstruction_.identity;
  receipt.moment_theory = moment_reconstruction_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = first_.accepted && second_.accepted && geometry_.accepted &&
      phase_crystal_.accepted && characteristic_.accepted && regular_singular_.accepted;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

}  // namespace holonics::event
