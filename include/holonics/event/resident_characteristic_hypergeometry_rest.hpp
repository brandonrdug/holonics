#pragma once

#include <holonics/event/resident_characteristic_hypergeometry.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline hypergeometry_rest_receipt
resident_characteristic_hypergeometry::rest(
    characteristic_hypergeometry_rest_record &record) noexcept {
  hypergeometry_rest_receipt receipt{};
  if (!admitted_ || pending_live_ || stage_ == stage::developmental)
    return receipt;
  record.standing = standing_;
  receipt.body = body_.rest(record.standing.standing.standing.body);
  if (!receipt.body.returned)
    return receipt;
  record.standing.standing.standing.integrity =
      rederivation_rest_integrity(record.standing.standing.standing);
  record.standing.standing.integrity =
      cultivated_organ_rest_integrity(record.standing.standing);
  record.standing.integrity =
      elementary_calculus_rest_integrity(record.standing);
  record.law = law_;
  record.application = application_;
  record.characteristic_admitted_tally = characteristic_admitted_tally_;
  record.trace_organ_admitted_tally = trace_organ_admitted_tally_;
  record.transport_admitted_tally = transport_admitted_tally_;
  record.applied = stage_ == stage::applied;
  record.integrity = characteristic_rest_integrity(record);
  receipt.discovery = law_.discovery.identity;
  receipt.organ = law_.organ.identity;
  receipt.application = application_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved =
      record.standing.application.accepted && law_.checker_founded;
  receipt.developmental_rows_absent = true;
  receipt.matrices_absent = true;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

} // namespace holonics::event
