#pragma once

#include <holonics/event/resident_elementary_calculus.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline elementary_calculus_rest_receipt resident_elementary_calculus::rest(
    elementary_calculus_rest_record &record) noexcept {
  elementary_calculus_rest_receipt receipt{};
  if (!admitted_ || pending_live_ || stage_ == stage::developmental) return receipt;
  record.standing = standing_; receipt.body = body_.rest(record.standing.standing.body);
  if (!receipt.body.returned) return receipt;
  record.standing.standing.integrity = rederivation_rest_integrity(record.standing.standing);
  record.standing.integrity = cultivated_organ_rest_integrity(record.standing);
  record.laws = laws_; record.application = application_;
  record.calculus_morphology = calculus_morphology_;
  record.self_organ_morphology = self_organ_morphology_;
  record.derivation_morphology = derivation_morphology_;
  record.applied = stage_ == stage::applied; record.integrity = elementary_calculus_rest_integrity(record);
  receipt.first_fiber = laws_.fibers[0].identity; receipt.self_organ = laws_.self_organ.identity;
  receipt.application = application_.identity; receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = record.standing.application.accepted && laws_.checker_founded;
  receipt.development_rows_absent = true; receipt.traces_absent = true;
  receipt.source_detached = true; receipt.returned = true; return receipt;
}

}  // namespace holonics::event
