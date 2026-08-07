#pragma once

#include <holonics/event/resident_trace_fiber.hpp>

namespace holonics::event {
HOLONICS_CALLABLE inline trace_fiber_rest_receipt
resident_trace_fiber::rest(trace_fiber_rest_record &record) noexcept {
  trace_fiber_rest_receipt receipt{};
  if (!admitted_ || pending_live_ || stage_ == stage::developmental)
    return receipt;
  record.standing = standing_;
  receipt.body = body_.rest(record.standing.standing.standing.standing.body);
  if (!receipt.body.returned)
    return receipt;
  record.standing.standing.standing.standing.integrity =
      rederivation_rest_integrity(record.standing.standing.standing.standing);
  record.standing.standing.standing.integrity =
      cultivated_organ_rest_integrity(record.standing.standing.standing);
  record.standing.standing.integrity =
      elementary_calculus_rest_integrity(record.standing.standing);
  record.standing.integrity = characteristic_rest_integrity(record.standing);
  record.law = law_;
  record.application = application_;
  record.applied = stage_ == stage::applied;
  record.integrity = trace_fiber_rest_integrity(record);
  receipt.discovery = law_.discovery.identity;
  receipt.sum_organ = law_.organs[0].identity;
  receipt.product_organ = law_.organs[1].identity;
  receipt.application = application_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = record.standing.applied && law_.checker_founded;
  receipt.developmental_rows_absent = true;
  receipt.target_traces_absent = true;
  receipt.matrices_absent = true;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

} // namespace holonics::event
