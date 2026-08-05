#pragma once

#include <holonics/event/resident_arithmetic_spectral.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline resident_arithmetic_spectral::resident_arithmetic_spectral(
    const organ::arithmetic_spectral_foundation& foundation,
    const hodge_realization_rest_record& record,
    hodge_realization_remount_receipt& receipt) noexcept
    : foundation_(foundation), body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal), characteristic_(record.characteristic),
      regular_singular_(record.regular_singular), code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction), cm_incidence_(record.cm_incidence),
      toric_cycle_(record.toric_cycle), algebraic_variation_(record.algebraic_variation),
      causal_linear_(record.causal_linear), intrinsic_hypergeometry_(record.intrinsic_hypergeometry),
      expression_geometry_(record.expression_geometry), hodge_realization_(record.hodge_realization),
      mathematical_morphology_(record.mathematical_morphology), codec_morphology_(record.codec_morphology),
      geometry_morphology_(record.geometry_morphology), phase_morphology_(record.phase_morphology),
      characteristic_morphology_(record.characteristic_morphology),
      regular_singular_morphology_(record.regular_singular_morphology),
      blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
      cm_incidence_morphology_(record.cm_incidence_morphology),
      toric_cycle_morphology_(record.toric_cycle_morphology),
      algebraic_variation_morphology_(record.algebraic_variation_morphology),
      causal_linear_morphology_(record.causal_linear_morphology),
      intrinsic_hypergeometry_morphology_(record.intrinsic_hypergeometry_morphology),
      expression_geometry_morphology_(record.expression_geometry_morphology),
      hodge_realization_morphology_(record.hodge_realization_morphology), source_detached_(true) {
  const bool exact = record.integrity == hodge_realization_rest_integrity(record);
  receipt.theory = hodge_realization_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && hodge_realization_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved &&
      organ::arithmetic_spectral_detail::valid_foundation(foundation_);
}

HOLONICS_CALLABLE inline resident_arithmetic_spectral::resident_arithmetic_spectral(
    const arithmetic_spectral_rest_record& record,
    arithmetic_spectral_remount_receipt& receipt) noexcept
    : body_(body::continuing_body::remount(record.body, receipt.body)), first_(record.first),
      second_(record.second), geometry_(record.geometry), phase_crystal_(record.phase_crystal),
      characteristic_(record.characteristic), regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction), moment_reconstruction_(record.moment_reconstruction),
      cm_incidence_(record.cm_incidence), toric_cycle_(record.toric_cycle),
      algebraic_variation_(record.algebraic_variation), causal_linear_(record.causal_linear),
      intrinsic_hypergeometry_(record.intrinsic_hypergeometry),
      expression_geometry_(record.expression_geometry), hodge_realization_(record.hodge_realization),
      arithmetic_spectral_(record.arithmetic_spectral),
      mathematical_morphology_(record.mathematical_morphology), codec_morphology_(record.codec_morphology),
      geometry_morphology_(record.geometry_morphology), phase_morphology_(record.phase_morphology),
      characteristic_morphology_(record.characteristic_morphology),
      regular_singular_morphology_(record.regular_singular_morphology),
      blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
      cm_incidence_morphology_(record.cm_incidence_morphology),
      toric_cycle_morphology_(record.toric_cycle_morphology),
      algebraic_variation_morphology_(record.algebraic_variation_morphology),
      causal_linear_morphology_(record.causal_linear_morphology),
      intrinsic_hypergeometry_morphology_(record.intrinsic_hypergeometry_morphology),
      expression_geometry_morphology_(record.expression_geometry_morphology),
      hodge_realization_morphology_(record.hodge_realization_morphology),
      arithmetic_spectral_morphology_(record.arithmetic_spectral_morphology),
      stage_(passage_stage::returned), source_detached_(true) {
  const bool exact = record.integrity == arithmetic_spectral_rest_integrity(record);
  receipt.theory = arithmetic_spectral_.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && arithmetic_spectral_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved;
}

}  // namespace holonics::event
