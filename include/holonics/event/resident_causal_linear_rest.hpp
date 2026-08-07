#pragma once

#include <holonics/event/resident_causal_linear.hpp>

namespace holonics::event {
HOLONICS_CALLABLE inline causal_linear_rest_receipt resident_causal_linear::rest(
    causal_linear_rest_record& record) noexcept {
  causal_linear_rest_receipt receipt{};
  if (!source_detached_ || !first_.accepted || !second_.accepted || !geometry_.accepted ||
      !phase_crystal_.accepted || !characteristic_.accepted || !regular_singular_.accepted ||
      !code_reconstruction_.accepted || !moment_reconstruction_.accepted ||
      !cm_incidence_.accepted || !toric_cycle_.accepted || !algebraic_variation_.accepted ||
      !causal_linear_.accepted || pending_live_ || stage_ != passage_stage::returned) {
    return receipt;
  }
  receipt.body = body_.rest(record.body); if (!receipt.body.returned) { return receipt; }
  record.first = first_; record.second = second_; record.geometry = geometry_;
  record.phase_crystal = phase_crystal_; record.characteristic = characteristic_;
  record.regular_singular = regular_singular_; record.code_reconstruction = code_reconstruction_;
  record.moment_reconstruction = moment_reconstruction_; record.cm_incidence = cm_incidence_;
  record.toric_cycle = toric_cycle_; record.algebraic_variation = algebraic_variation_;
  record.causal_linear = causal_linear_;
  record.integrity = causal_linear_rest_integrity(record);
  receipt.theory = causal_linear_.identity; receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = first_.accepted && second_.accepted && geometry_.accepted &&
      phase_crystal_.accepted && characteristic_.accepted && regular_singular_.accepted &&
      code_reconstruction_.accepted && moment_reconstruction_.accepted && cm_incidence_.accepted &&
      toric_cycle_.accepted && algebraic_variation_.accepted;
  receipt.source_detached = true; receipt.returned = true; return receipt;
}

}  // namespace holonics::event
