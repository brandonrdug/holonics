#pragma once

#include <holonics/event/resident_trace_rebase.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline trace_rebase_rest_receipt
resident_trace_rebase::rest(trace_rebase_rest_record &record) noexcept {
  trace_rebase_rest_receipt receipt{};
  if (!admitted_ || pending_live_ || stage_ == stage::developmental)
    return receipt;
  record.standing = standing_;
  receipt.body = body_.rest(
      record.standing.standing.standing.standing.standing.body);
  if (!receipt.body.returned)
    return receipt;
  record.standing.standing.standing.standing.standing.integrity =
      rederivation_rest_integrity(
          record.standing.standing.standing.standing.standing);
  record.standing.standing.standing.standing.integrity =
      cultivated_organ_rest_integrity(
          record.standing.standing.standing.standing);
  record.standing.standing.standing.integrity =
      elementary_calculus_rest_integrity(record.standing.standing.standing);
  record.standing.standing.integrity =
      characteristic_rest_integrity(record.standing.standing);
  record.standing.integrity = trace_fiber_rest_integrity(record.standing);
  record.law = law_;
  record.application = application_;
  record.rebase_admitted_tally = rebase_admitted_tally_;
  record.differential_admitted_tally = differential_admitted_tally_;
  record.deck_admitted_tally = deck_admitted_tally_;
  record.path_admitted_tally = path_admitted_tally_;
  record.applied = stage_ == stage::applied;
  record.integrity = trace_rebase_rest_integrity(record);
  receipt.discovery = law_.discovery.identity;
  receipt.tangent = law_.tangent.identity;
  receipt.deck = law_.deck.return_receipt.identity;
  receipt.application = application_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = record.standing.applied &&
                                    law_.checker_founded;
  receipt.developmental_rows_absent = true;
  receipt.matrices_absent = true;
  receipt.tangent_rows_absent = true;
  receipt.source_detached = true;
  receipt.returned = true;
  return receipt;
}

} // namespace holonics::event
