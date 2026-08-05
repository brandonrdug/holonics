#pragma once

#include <holonics/event/resident_rederivation.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline resident_rederivation::resident_rederivation(
    const organ::rederivation_foundation &foundation,
    const arithmetic_spectral_rest_record &record,
    arithmetic_spectral_remount_receipt &receipt) noexcept
    : foundation_(foundation),
      body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal),
      characteristic_(record.characteristic),
      regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction),
      cm_incidence_(record.cm_incidence), toric_cycle_(record.toric_cycle),
      algebraic_variation_(record.algebraic_variation),
      causal_linear_(record.causal_linear),
      intrinsic_hypergeometry_(record.intrinsic_hypergeometry),
      expression_geometry_(record.expression_geometry),
      hodge_realization_(record.hodge_realization),
      arithmetic_spectral_(record.arithmetic_spectral),
      mathematical_morphology_(record.mathematical_morphology),
      codec_morphology_(record.codec_morphology),
      geometry_morphology_(record.geometry_morphology),
      phase_morphology_(record.phase_morphology),
      characteristic_morphology_(record.characteristic_morphology),
      regular_singular_morphology_(record.regular_singular_morphology),
      blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
      cm_incidence_morphology_(record.cm_incidence_morphology),
      toric_cycle_morphology_(record.toric_cycle_morphology),
      algebraic_variation_morphology_(record.algebraic_variation_morphology),
      causal_linear_morphology_(record.causal_linear_morphology),
      intrinsic_hypergeometry_morphology_(
          record.intrinsic_hypergeometry_morphology),
      expression_geometry_morphology_(record.expression_geometry_morphology),
      hodge_realization_morphology_(record.hodge_realization_morphology),
      arithmetic_spectral_morphology_(record.arithmetic_spectral_morphology),
      source_detached_(true) {
  const bool exact =
      record.integrity == arithmetic_spectral_rest_integrity(record);
  receipt.theory = arithmetic_spectral_.identity;
  receipt.same_body =
      receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && arithmetic_spectral_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved &&
              organ::rederivation_detail::valid(foundation_);
}

HOLONICS_CALLABLE inline resident_rederivation::resident_rederivation(
    const rederivation_rest_record &record,
    rederivation_remount_receipt &receipt) noexcept
    : body_(body::continuing_body::remount(record.body, receipt.body)),
      first_(record.first), second_(record.second), geometry_(record.geometry),
      phase_crystal_(record.phase_crystal),
      characteristic_(record.characteristic),
      regular_singular_(record.regular_singular),
      code_reconstruction_(record.code_reconstruction),
      moment_reconstruction_(record.moment_reconstruction),
      cm_incidence_(record.cm_incidence), toric_cycle_(record.toric_cycle),
      algebraic_variation_(record.algebraic_variation),
      causal_linear_(record.causal_linear),
      intrinsic_hypergeometry_(record.intrinsic_hypergeometry),
      expression_geometry_(record.expression_geometry),
      hodge_realization_(record.hodge_realization),
      arithmetic_spectral_(record.arithmetic_spectral),
      matching_rederivation_(record.matching_rederivation),
      lattice_rederivation_(record.lattice_rederivation),
      potential_rederivation_(record.potential_rederivation),
      cover_rederivation_(record.cover_rederivation),
      mathematical_morphology_(record.mathematical_morphology),
      codec_morphology_(record.codec_morphology),
      geometry_morphology_(record.geometry_morphology),
      phase_morphology_(record.phase_morphology),
      characteristic_morphology_(record.characteristic_morphology),
      regular_singular_morphology_(record.regular_singular_morphology),
      blind_reconstruction_morphology_(record.blind_reconstruction_morphology),
      cm_incidence_morphology_(record.cm_incidence_morphology),
      toric_cycle_morphology_(record.toric_cycle_morphology),
      algebraic_variation_morphology_(record.algebraic_variation_morphology),
      causal_linear_morphology_(record.causal_linear_morphology),
      intrinsic_hypergeometry_morphology_(
          record.intrinsic_hypergeometry_morphology),
      expression_geometry_morphology_(record.expression_geometry_morphology),
      hodge_realization_morphology_(record.hodge_realization_morphology),
      arithmetic_spectral_morphology_(record.arithmetic_spectral_morphology),
      rederivation_morphology_(record.rederivation_morphology),
      stage_(passage_stage::returned), source_detached_(true) {
  const bool exact = record.integrity == rederivation_rest_integrity(record);
  receipt.theory = matching_rederivation_.identity;
  receipt.same_body =
      receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && matching_rederivation_.accepted &&
                             lattice_rederivation_.accepted &&
                             potential_rederivation_.accepted &&
                             cover_rederivation_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = exact && receipt.theory_preserved;
}

} // namespace holonics::event
