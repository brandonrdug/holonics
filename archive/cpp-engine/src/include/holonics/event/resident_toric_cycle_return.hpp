#pragma once

#include <holonics/event/resident_toric_cycle.hpp>

namespace holonics::event {
HOLONICS_CALLABLE inline resident_toric_cycle::resident_toric_cycle(
    const organ::toric_cycle_foundation& foundation,
    const cm_incidence_rest_record& record, cm_incidence_remount_receipt& receipt) noexcept
    : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
      regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence), source_detached_(true) {
  const bool exact = record.integrity == cm_incidence_rest_integrity(record);
  receipt.theory = cm_incidence_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && cm_incidence_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved && organ::toric_fan_detail::valid_foundation(foundation_);
}

HOLONICS_CALLABLE inline resident_toric_cycle::resident_toric_cycle(
    const toric_cycle_rest_record& record, toric_cycle_remount_receipt& receipt) noexcept
    : body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
      regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), source_detached_(true) {
  const bool exact = record.integrity == toric_cycle_rest_integrity(record);
  receipt.theory = toric_cycle_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && toric_cycle_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved;
  stage_ = passage_stage::returned;
}

HOLONICS_CALLABLE inline bool resident_toric_cycle::form(
    const organ::toric_cycle_question& question,
    toric_cycle_observation& observation) noexcept {
  if (!admitted_ || pending_live_ || stage_ != passage_stage::none) { return false; }
  organ::toric_cycle_detail::close(foundation_, question, observation.inquiry);
  const auto& inquiry = observation.inquiry;
  codec::toric_cycle_surface surface{};
  surface.passage = inquiry.theory.passage;
  for (std::uint8_t fan = 0; fan < 2; ++fan) {
    surface.ray_counts[fan] = inquiry.fans[fan].source.ray_count;
    surface.quotient_ranks[fan] = inquiry.quotients[fan].rank;
    surface.middle_betti[fan] = inquiry.comparisons[fan].betti[2];
    surface.middle_hodge[fan] = inquiry.comparisons[fan].hodge[1][1];
    for (std::uint8_t ray = 0; ray < inquiry.fans[fan].source.ray_count; ++ray) {
      surface.rays[fan][ray][0] = inquiry.fans[fan].source.rays[ray].x;
      surface.rays[fan][ray][1] = inquiry.fans[fan].source.rays[ray].y;
      surface.cone_determinants[fan][ray] = inquiry.fans[fan].cone_determinants[ray];
      for (std::uint8_t coordinate = 0; coordinate < inquiry.quotients[fan].rank;
          ++coordinate) {
        surface.divisor_classes[fan][ray][coordinate] =
            inquiry.quotients[fan].divisor_classes[ray][coordinate].numerator;
      }
      for (std::uint8_t relation = 0; relation < 2; ++relation) {
        surface.principal_relations[fan][relation][ray] =
            inquiry.quotients[fan].principal_relations[relation][ray];
      }
    }
  }
  surface.ray_counts[2] = inquiry.blowup.fan.source.ray_count;
  surface.quotient_ranks[2] = inquiry.blowup.quotient.rank;
  surface.middle_betti[2] = inquiry.blowup.comparison.betti[2];
  surface.middle_hodge[2] = inquiry.blowup.comparison.hodge[1][1];
  for (std::uint8_t ray = 0; ray < inquiry.blowup.fan.source.ray_count; ++ray) {
    surface.rays[2][ray][0] = inquiry.blowup.fan.source.rays[ray].x;
    surface.rays[2][ray][1] = inquiry.blowup.fan.source.rays[ray].y;
    surface.cone_determinants[2][ray] = inquiry.blowup.fan.cone_determinants[ray];
  }
  for (std::uint8_t row = 0; row < 2; ++row) {
    surface.integral_class[row] = inquiry.realizations[0].class_coordinates[row].numerator;
    surface.integral_response[row] = inquiry.realizations[0].target.response[row + 2U].numerator;
    surface.negative_class[row] = inquiry.polarization.primitive_negative[row].numerator;
    surface.exceptional[row] = inquiry.blowup.exceptional[row].numerator;
    surface.blowup_negative[row] =
        inquiry.blowup.polarization.primitive_negative[row].numerator;
    for (std::uint8_t column = 0; column < 2; ++column) {
      surface.base_form[row][column] =
          inquiry.intersections[1].quotient_form[row][column].numerator;
      surface.blowup_form[row][column] =
          inquiry.blowup.intersection.quotient_form[row][column].numerator;
    }
  }
  surface.rational_numerator = inquiry.realizations[1].class_coordinates[0].numerator;
  surface.rational_denominator = inquiry.realizations[1].class_coordinates[0].denominator;
  for (std::uint8_t ray = 0; ray < 4; ++ray) {
    surface.incompatible_response[ray] =
        inquiry.realizations[2].target.response[ray].numerator;
  }
  surface.negative_square = inquiry.polarization.primitive_square.numerator;
  surface.exceptional_square = inquiry.blowup.exceptional_square.numerator;
  surface.blowup_negative_square = inquiry.blowup.polarization.primitive_square.numerator;
  surface.derived_ray[0] = inquiry.blowup.derived_ray.x;
  surface.derived_ray[1] = inquiry.blowup.derived_ray.y;
  for (std::uint8_t ray = 0; ray < inquiry.blowup.old_ray_count; ++ray) {
    for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
      surface.strict_transforms[ray][coordinate] =
          inquiry.blowup.transforms[ray].strict[coordinate].numerator;
      surface.total_transforms[ray][coordinate] =
          inquiry.blowup.transforms[ray].total[coordinate].numerator;
    }
  }
  for (std::uint8_t coordinate = 0; coordinate < 2; ++coordinate) {
    surface.pullback[coordinate] = inquiry.blowup.pullback[coordinate].numerator;
    surface.pushforward[coordinate] = inquiry.blowup.pushforward[coordinate].numerator;
  }
  surface.fan_chow_agree = inquiry.intersections[0].fan_chow_agree &&
      inquiry.intersections[1].fan_chow_agree && inquiry.blowup.intersection.fan_chow_agree;
  surface.inverse_fibers_exact = inquiry.realizations[0].exact &&
      inquiry.realizations[1].exact && inquiry.realizations[2].exact;
  surface.blowup_transport_exact = inquiry.blowup.exact;
  surface.alternatives_retained = inquiry.alternatives_retained;
  if (!inquiry.theory_formed ||
      !codec::render_toric_cycle(surface, observation.passage.formal) ||
      !codec::render_toric_explanation(surface, observation.passage.conversational)) {
    observation.inquiry.obstruction = organ::toric_obstruction::render_refused; return false;
  }
  auto continuation = body_.take_continuation();
  observation.passage.formation_commit = body_.commit(body_.head(), 0,
      inquiry.theory.passage.value(), static_cast<body::linear_continuation&&>(continuation));
  if (observation.passage.formation_commit.state != body::body_change_status::committed) {
    observation.inquiry.obstruction = organ::toric_obstruction::continuation_refused;
    return false;
  }
  const checker_outbound_occurrence outbound{body_.head(), exact::word{161'000},
      exact::word{161'001}, exact::word{161'002}, exact::word{161'003},
      exact::word{161'004}, inquiry.theory.passage, observation.passage.formal.identity};
  ::new (static_cast<void*>(pending_storage_)) checker_pending_deed{
      body_.take_continuation(), outbound};
  pending_live_ = true;
  observation.passage.outbound = outbound;
  observation.passage.checker_stage = checker_stage_status::exact;
  observation.passage.pending_before_process = true;
  return true;
}

HOLONICS_CALLABLE inline bool resident_toric_cycle::resume(
    const checker_raw_return& raw, toric_cycle_observation& observation) noexcept {
  observation.passage.raw = raw;
  auto* pending = live_pending();
  if (pending == nullptr || !pending->resumable()) { return false; }
  const auto expected = pending->outbound();
  auto& typed = observation.passage.typed;
  typed.passage = raw.passage; typed.source = raw.source;
  const bool lineage_exact = raw.predecessor == expected.predecessor &&
      raw.event == expected.event && raw.port == expected.expected_return_port &&
      raw.lineage.value() == expected.lineage.value() + 1U &&
      raw.passage == expected.passage && raw.source == expected.source;
  if (!lineage_exact) { typed.state = checker_return_status::passage_mismatch; return false; }
  constexpr char declaration[] = "Soma.Holonics.R23.generated_toric_cycle_transport";
  constexpr char source[] = "theorem generated_toric_cycle_transport";
  cm_checker_detail::normalize(raw, observation.passage.formal, declaration, source, typed);
  const bool accepted = typed.state == checker_return_status::accepted;
  auto& morphology = observation.passage.returned_morphology;
  morphology.commit = body_.commit(expected.predecessor, 0,
      expected.passage.value(), pending->take_continuation());
  pending_live_ = false;
  morphology.returned_difference_applied = accepted &&
      morphology.commit.state == body::body_change_status::committed;
  observation.passage.pending_after_return = pending_live_;
  observation.passage.passage_preserved = typed.passage == expected.passage &&
      observation.passage.formal.passage == expected.passage;
  if (accepted && morphology.returned_difference_applied) {
    toric_cycle_ = {exact::word{190'300}, expected.passage, raw.event,
        observation.inquiry.theory.lineage, true};
    observation.passage.acquired = toric_cycle_;
    stage_ = passage_stage::returned;
  }
  return morphology.returned_difference_applied && accepted;
}

HOLONICS_CALLABLE inline toric_cycle_rest_receipt resident_toric_cycle::rest(
    toric_cycle_rest_record& record) noexcept {
  toric_cycle_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted || !geometry_.accepted ||
      !phase_crystal_.accepted || !characteristic_.accepted || !regular_singular_.accepted ||
      !code_reconstruction_.accepted || !moment_reconstruction_.accepted ||
      !cm_incidence_.accepted || !toric_cycle_.accepted || pending_live_ ||
      stage_ != passage_stage::returned) { return receipt; }
  receipt.body = body_.rest(record.body);
  if (!receipt.body.returned) { return receipt; }
  record.first = first_; record.second = second_; record.geometry = geometry_;
  record.phase_crystal = phase_crystal_; record.characteristic = characteristic_;
  record.regular_singular = regular_singular_;
  record.code_reconstruction = code_reconstruction_;
  record.moment_reconstruction = moment_reconstruction_;
  record.cm_incidence = cm_incidence_; record.toric_cycle = toric_cycle_;
  record.integrity = toric_cycle_rest_integrity(record);
  receipt.theory = toric_cycle_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = first_.accepted && second_.accepted &&
      geometry_.accepted && phase_crystal_.accepted && characteristic_.accepted &&
      regular_singular_.accepted && code_reconstruction_.accepted &&
      moment_reconstruction_.accepted && cm_incidence_.accepted;
  receipt.source_detached = true; receipt.returned = true;
  return receipt;
}

}  // namespace holonics::event
