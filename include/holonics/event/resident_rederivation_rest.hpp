#pragma once

#include <holonics/event/resident_rederivation.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline rederivation_rest_receipt
resident_rederivation::rest(rederivation_rest_record &record) noexcept {
  rederivation_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted ||
      !geometry_.accepted || !phase_crystal_.accepted ||
      !characteristic_.accepted || !regular_singular_.accepted ||
      !code_reconstruction_.accepted || !moment_reconstruction_.accepted ||
      !cm_incidence_.accepted || !toric_cycle_.accepted ||
      !algebraic_variation_.accepted || !causal_linear_.accepted ||
      !intrinsic_hypergeometry_.accepted || !expression_geometry_.accepted ||
      !hodge_realization_.accepted || !arithmetic_spectral_.accepted ||
      !matching_rederivation_.accepted || !lattice_rederivation_.accepted ||
      !potential_rederivation_.accepted || !cover_rederivation_.accepted ||
      pending_live_ || stage_ != passage_stage::returned) {
    return receipt;
  }
  receipt.body = body_.rest(record.body);
  if (!receipt.body.returned) {
    return receipt;
  }
  record.first = first_;
  record.second = second_;
  record.geometry = geometry_;
  record.phase_crystal = phase_crystal_;
  record.characteristic = characteristic_;
  record.regular_singular = regular_singular_;
  record.code_reconstruction = code_reconstruction_;
  record.moment_reconstruction = moment_reconstruction_;
  record.cm_incidence = cm_incidence_;
  record.toric_cycle = toric_cycle_;
  record.algebraic_variation = algebraic_variation_;
  record.causal_linear = causal_linear_;
  record.intrinsic_hypergeometry = intrinsic_hypergeometry_;
  record.expression_geometry = expression_geometry_;
  record.hodge_realization = hodge_realization_;
  record.arithmetic_spectral = arithmetic_spectral_;
  record.matching_rederivation = matching_rederivation_;
  record.lattice_rederivation = lattice_rederivation_;
  record.potential_rederivation = potential_rederivation_;
  record.cover_rederivation = cover_rederivation_;
  record.mathematical_admitted_tally = mathematical_admitted_tally_;
  record.codec_admitted_tally = codec_admitted_tally_;
  record.geometry_admitted_tally = geometry_admitted_tally_;
  record.phase_admitted_tally = phase_admitted_tally_;
  record.characteristic_admitted_tally = characteristic_admitted_tally_;
  record.regular_singular_admitted_tally = regular_singular_admitted_tally_;
  record.blind_reconstruction_admitted_tally = blind_reconstruction_admitted_tally_;
  record.cm_incidence_admitted_tally = cm_incidence_admitted_tally_;
  record.toric_cycle_admitted_tally = toric_cycle_admitted_tally_;
  record.algebraic_variation_admitted_tally = algebraic_variation_admitted_tally_;
  record.causal_linear_admitted_tally = causal_linear_admitted_tally_;
  record.intrinsic_hypergeometry_admitted_tally =
      intrinsic_hypergeometry_admitted_tally_;
  record.expression_geometry_admitted_tally = expression_geometry_admitted_tally_;
  record.hodge_realization_admitted_tally = hodge_realization_admitted_tally_;
  record.arithmetic_spectral_admitted_tally = arithmetic_spectral_admitted_tally_;
  record.rederivation_admitted_tally = rederivation_admitted_tally_;
  record.integrity = rederivation_rest_integrity(record);
  receipt.theory = matching_rederivation_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved =
      first_.accepted && second_.accepted && geometry_.accepted &&
      phase_crystal_.accepted && characteristic_.accepted &&
      regular_singular_.accepted && code_reconstruction_.accepted &&
      moment_reconstruction_.accepted && cm_incidence_.accepted &&
      toric_cycle_.accepted && algebraic_variation_.accepted &&
      causal_linear_.accepted && intrinsic_hypergeometry_.accepted &&
      expression_geometry_.accepted && hodge_realization_.accepted &&
      arithmetic_spectral_.accepted;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

} // namespace holonics::event
