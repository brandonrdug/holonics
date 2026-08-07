#pragma once

#include <holonics/event/resident_trace_rebase.hpp>
#include <holonics/organ/trace_rebase_matrix_law.hpp>

namespace holonics::event {
namespace trace_rebase_mount_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool metadata(
    const organ::cultivation_card_metadata &m) noexcept {
  return m.parsed && m.schema.value() != 0 && m.occurrence.value() != 0 &&
         m.incoming_port.value() != 0 && m.return_port.value() != 0 &&
         m.lineage.value() != 0;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool valid(
    const organ::trace_rebase_development_bundle &cards) noexcept {
  bool exact = true;
  for (const auto &source : cards.sources) {
    exact = exact && metadata(source.metadata);
    for (const auto &seed : source.seeds)
      exact = exact && organ::trace_rebase_matrix_detail::valid(seed);
  }
  return exact;
}
} // namespace trace_rebase_mount_detail
HOLONICS_CALLABLE inline resident_trace_rebase::resident_trace_rebase(
    const organ::trace_rebase_development_bundle &cards,
    const trace_fiber_rest_record &record,
    trace_fiber_remount_receipt &receipt) noexcept
    : standing_(record), cards_(cards),
      body_(body::continuing_body::remount(
          record.standing.standing.standing.standing.body, receipt.body)) {
  const bool exact = record.integrity == trace_fiber_rest_integrity(record);
  receipt.discovery = record.law.discovery.identity;
  receipt.sum_organ = record.law.organs[0].identity;
  receipt.product_organ = record.law.organs[1].identity;
  receipt.application = record.application.identity;
  receipt.same_body = exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.prior_returns_preserved = record.standing.applied &&
                                    record.standing.application.accepted;
  receipt.laws_preserved = record.law.checker_founded &&
      record.law.organs[0].checker_founded && record.law.organs[1].checker_founded;
  receipt.application_preserved = record.applied && record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.prior_returns_preserved &&
              receipt.laws_preserved && receipt.application_preserved &&
              !receipt.source_replayed && trace_rebase_mount_detail::valid(cards);
  standing_.standing.standing.standing.standing.body = {};
  standing_.standing.standing.standing.standing.integrity = 0;
  standing_.standing.standing.standing.integrity = 0;
  standing_.standing.standing.integrity = 0;
  standing_.standing.integrity = 0;
  standing_.integrity = 0;
}
HOLONICS_CALLABLE inline resident_trace_rebase::resident_trace_rebase(
    const trace_rebase_rest_record &record,
    trace_rebase_remount_receipt &receipt) noexcept
    : standing_(record.standing),
      body_(body::continuing_body::remount(
          record.standing.standing.standing.standing.standing.body,
          receipt.body)),
      law_(record.law), application_(record.application),
      stage_(record.applied ? stage::applied : stage::derived) {
  const bool exact = record.integrity == trace_rebase_rest_integrity(record);
  receipt.discovery = record.law.discovery.identity;
  receipt.tangent = record.law.tangent.identity;
  receipt.deck = record.law.deck.return_receipt.identity;
  receipt.application = record.application.identity;
  receipt.same_body = exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.prior_returns_preserved = record.standing.applied &&
                                    record.standing.application.accepted;
  receipt.maps_preserved = record.law.checker_founded &&
      record.law.discovery.identity == exact::word{202'300};
  for (std::uint8_t i = 0; i < organ::trace_rebase_move_count; ++i)
    receipt.maps_preserved = receipt.maps_preserved &&
        record.law.maps[i].checker_founded &&
        record.law.maps[i].identity == exact::word{202'301U + i};
  receipt.differential_preserved = record.law.tangent.accepted &&
      record.law.deck.return_receipt.accepted && record.law.deck.primitive;
  receipt.application_preserved = !record.applied || record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.prior_returns_preserved &&
              receipt.maps_preserved && receipt.differential_preserved &&
              receipt.application_preserved && !receipt.source_replayed;
  standing_.standing.standing.standing.standing.body = {};
  standing_.standing.standing.standing.standing.integrity = 0;
  standing_.standing.standing.standing.integrity = 0;
  standing_.standing.standing.integrity = 0;
  standing_.standing.integrity = 0;
  standing_.integrity = 0;
}

} // namespace holonics::event
