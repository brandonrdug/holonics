#pragma once

#include <holonics/event/resident_causal_linear.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline resident_causal_linear::resident_causal_linear(
    const organ::causal_linear_foundation& foundation,
    const algebraic_variation_rest_record& record,
    algebraic_variation_remount_receipt& receipt) noexcept
    : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
      regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), algebraic_variation_(record.algebraic_variation),
      mathematical_morphology_(record.mathematical_morphology),
      codec_morphology_(record.codec_morphology), geometry_morphology_(record.geometry_morphology),
      phase_morphology_(record.phase_morphology),
      characteristic_morphology_(record.characteristic_morphology),
      regular_singular_morphology_(record.regular_singular_morphology),
      blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
      cm_incidence_morphology_(record.cm_incidence_morphology),
      toric_cycle_morphology_(record.toric_cycle_morphology),
      algebraic_variation_morphology_(record.algebraic_variation_morphology),
      source_detached_(true) {
  const bool exact = record.integrity == algebraic_variation_rest_integrity(record);
  receipt.theory = algebraic_variation_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && algebraic_variation_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved &&
      organ::causal_linear_detail::valid_foundation(foundation_);
}

HOLONICS_CALLABLE inline resident_causal_linear::resident_causal_linear(
    const causal_linear_rest_record& record, causal_linear_remount_receipt& receipt) noexcept
    : body_(body::continuing_body::remount(record.body, receipt.body)), first_(record.first),
      second_(record.second), geometry_(record.geometry), phase_crystal_(record.phase_crystal),
      characteristic_(record.characteristic), regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), algebraic_variation_(record.algebraic_variation),
      causal_linear_(record.causal_linear),
      mathematical_morphology_(record.mathematical_morphology),
      codec_morphology_(record.codec_morphology), geometry_morphology_(record.geometry_morphology),
      phase_morphology_(record.phase_morphology),
      characteristic_morphology_(record.characteristic_morphology),
      regular_singular_morphology_(record.regular_singular_morphology),
      blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
      cm_incidence_morphology_(record.cm_incidence_morphology),
      toric_cycle_morphology_(record.toric_cycle_morphology),
      algebraic_variation_morphology_(record.algebraic_variation_morphology),
      causal_linear_morphology_(record.causal_linear_morphology),
      stage_(passage_stage::returned), source_detached_(true) {
  const bool exact = record.integrity == causal_linear_rest_integrity(record);
  receipt.theory = causal_linear_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && causal_linear_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved;
}

}  // namespace holonics::event
