#pragma once

#include <holonics/event/resident_characteristic_hypergeometry.hpp>
#include <holonics/organ/characteristic_matrix_law.hpp>

namespace holonics::event {
namespace characteristic_mount_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool
metadata(const organ::cultivation_card_metadata &m) noexcept {
  return m.parsed && m.schema.value() != 0 && m.occurrence.value() != 0 &&
         m.incoming_port.value() != 0 && m.return_port.value() != 0 &&
         m.lineage.value() != 0;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool
valid(const organ::characteristic_development_bundle &cards) noexcept {
  bool exact = true;
  for (const auto &card : cards.sources)
    exact = exact && metadata(card.metadata) && card.alphabet_size >= 2 &&
            card.alphabet_size <= 4 && card.maximum_length >= 3 &&
            card.maximum_length <= 4 &&
            ::holonics::organ::elementary_matrix_detail::determinant(
                card.rechart) == 1;
  return exact;
}
} // namespace characteristic_mount_detail
HOLONICS_CALLABLE inline resident_characteristic_hypergeometry::
    resident_characteristic_hypergeometry(
        const organ::characteristic_development_bundle &cards,
        const elementary_calculus_rest_record &record,
        elementary_calculus_remount_receipt &receipt) noexcept
    : standing_(record), cards_(cards),
      body_(body::continuing_body::remount(record.standing.standing.body,
                                           receipt.body)) {
  const bool exact =
      record.integrity == elementary_calculus_rest_integrity(record);
  receipt.first_fiber = record.laws.fibers[0].identity;
  receipt.self_organ = record.laws.self_organ.identity;
  receipt.application = record.application.identity;
  receipt.same_body =
      exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.prior_returns_preserved = record.standing.application.accepted;
  receipt.laws_preserved =
      record.laws.checker_founded && record.laws.self_organ.checker_founded;
  receipt.application_preserved = record.applied && record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.prior_returns_preserved &&
              receipt.laws_preserved && receipt.application_preserved &&
              !receipt.source_replayed &&
              characteristic_mount_detail::valid(cards);
  standing_.standing.standing.body = {};
  standing_.standing.standing.integrity = 0;
  standing_.standing.integrity = 0;
  standing_.integrity = 0;
}
HOLONICS_CALLABLE inline resident_characteristic_hypergeometry::
    resident_characteristic_hypergeometry(
        const characteristic_hypergeometry_rest_record &record,
        hypergeometry_remount_receipt &receipt) noexcept
    : standing_(record.standing),
      body_(body::continuing_body::remount(
          record.standing.standing.standing.body, receipt.body)),
      law_(record.law), application_(record.application),
      characteristic_morphology_(record.characteristic_morphology),
      trace_organ_morphology_(record.trace_organ_morphology),
      transport_morphology_(record.transport_morphology),
      stage_(record.applied ? stage::applied : stage::derived) {
  const bool exact = record.integrity == characteristic_rest_integrity(record);
  receipt.discovery = record.law.discovery.identity;
  receipt.organ = record.law.organ.identity;
  receipt.application = record.application.identity;
  receipt.same_body =
      exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.prior_returns_preserved =
      record.standing.applied && record.standing.application.accepted;
  receipt.law_preserved =
      record.law.checker_founded && record.law.discovery.accepted &&
      record.law.discovery.identity == exact::word{200'300} &&
      record.law.organ.checker_founded &&
      record.law.organ.identity == exact::word{200'301};
  receipt.application_preserved =
      !record.applied || record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.prior_returns_preserved &&
              receipt.law_preserved && receipt.application_preserved &&
              !receipt.source_replayed;
  standing_.standing.standing.body = {};
  standing_.standing.standing.integrity = 0;
  standing_.standing.integrity = 0;
  standing_.integrity = 0;
}

} // namespace holonics::event
