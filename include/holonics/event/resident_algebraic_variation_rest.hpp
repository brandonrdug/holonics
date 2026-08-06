#pragma once

#include <holonics/event/resident_algebraic_variation.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline resident_algebraic_variation::resident_algebraic_variation(
    const organ::algebraic_variation_foundation& foundation,
    const toric_cycle_rest_record& record, toric_cycle_remount_receipt& receipt) noexcept
    : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
      regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), mathematical_admitted_tally_(record.mathematical_admitted_tally),
      codec_admitted_tally_(record.codec_admitted_tally), geometry_admitted_tally_(record.geometry_admitted_tally),
      phase_admitted_tally_(record.phase_admitted_tally),
      characteristic_admitted_tally_(record.characteristic_admitted_tally),
      regular_singular_admitted_tally_(record.regular_singular_admitted_tally),
      blind_reconstruction_admitted_tally_(record.blind_reconstruction_admitted_tally),
      cm_incidence_admitted_tally_(record.cm_incidence_admitted_tally),
      toric_cycle_admitted_tally_(record.toric_cycle_admitted_tally), source_detached_(true) {
  const bool exact = record.integrity == toric_cycle_rest_integrity(record);
  receipt.theory = toric_cycle_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && toric_cycle_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved &&
      organ::variation_polynomial_detail::valid_foundation(foundation_);
}

HOLONICS_CALLABLE inline resident_algebraic_variation::resident_algebraic_variation(
    const algebraic_variation_rest_record& record,
    algebraic_variation_remount_receipt& receipt) noexcept
    : body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
      regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), algebraic_variation_(record.algebraic_variation),
      mathematical_admitted_tally_(record.mathematical_admitted_tally),
      codec_admitted_tally_(record.codec_admitted_tally), geometry_admitted_tally_(record.geometry_admitted_tally),
      phase_admitted_tally_(record.phase_admitted_tally),
      characteristic_admitted_tally_(record.characteristic_admitted_tally),
      regular_singular_admitted_tally_(record.regular_singular_admitted_tally),
      blind_reconstruction_admitted_tally_(record.blind_reconstruction_admitted_tally),
      cm_incidence_admitted_tally_(record.cm_incidence_admitted_tally),
      toric_cycle_admitted_tally_(record.toric_cycle_admitted_tally),
      algebraic_variation_admitted_tally_(record.algebraic_variation_admitted_tally),
      stage_(passage_stage::returned), source_detached_(true) {
  const bool exact = record.integrity == algebraic_variation_rest_integrity(record);
  receipt.theory = algebraic_variation_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && algebraic_variation_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved;
}

HOLONICS_CALLABLE inline algebraic_variation_rest_receipt
resident_algebraic_variation::rest(algebraic_variation_rest_record& record) noexcept {
  algebraic_variation_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted || !geometry_.accepted ||
      !phase_crystal_.accepted || !characteristic_.accepted || !regular_singular_.accepted ||
      !code_reconstruction_.accepted || !moment_reconstruction_.accepted ||
      !cm_incidence_.accepted || !toric_cycle_.accepted || !algebraic_variation_.accepted ||
      pending_live_ || stage_ != passage_stage::returned) { return receipt; }
  receipt.body = body_.rest(record.body); if (!receipt.body.returned) { return receipt; }
  record.first = first_; record.second = second_; record.geometry = geometry_;
  record.phase_crystal = phase_crystal_; record.characteristic = characteristic_;
  record.regular_singular = regular_singular_; record.code_reconstruction = code_reconstruction_;
  record.moment_reconstruction = moment_reconstruction_; record.cm_incidence = cm_incidence_;
  record.toric_cycle = toric_cycle_; record.algebraic_variation = algebraic_variation_;
  record.mathematical_admitted_tally = mathematical_admitted_tally_;
  record.codec_admitted_tally = codec_admitted_tally_; record.geometry_admitted_tally = geometry_admitted_tally_;
  record.phase_admitted_tally = phase_admitted_tally_;
  record.characteristic_admitted_tally = characteristic_admitted_tally_;
  record.regular_singular_admitted_tally = regular_singular_admitted_tally_;
  record.blind_reconstruction_admitted_tally = blind_reconstruction_admitted_tally_;
  record.cm_incidence_admitted_tally = cm_incidence_admitted_tally_;
  record.toric_cycle_admitted_tally = toric_cycle_admitted_tally_;
  record.algebraic_variation_admitted_tally = algebraic_variation_admitted_tally_;
  record.integrity = algebraic_variation_rest_integrity(record);
  receipt.theory = algebraic_variation_.identity; receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = first_.accepted && second_.accepted && geometry_.accepted &&
      phase_crystal_.accepted && characteristic_.accepted && regular_singular_.accepted &&
      code_reconstruction_.accepted && moment_reconstruction_.accepted && cm_incidence_.accepted &&
      toric_cycle_.accepted;
  receipt.source_detached = true; receipt.returned = true; return receipt;
}

}  // namespace holonics::event
