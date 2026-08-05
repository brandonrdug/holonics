#pragma once

#include <holonics/event/resident_elementary_calculus.hpp>

namespace holonics::event {
namespace elementary_mount_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool metadata_exact(
    const organ::cultivation_card_metadata &metadata) noexcept {
  return metadata.parsed && metadata.schema.value() != 0 && metadata.occurrence.value() != 0 &&
      metadata.incoming_port.value() != 0 && metadata.return_port.value() != 0 &&
      metadata.lineage.value() != 0;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool valid(
    const organ::elementary_development_bundle &cards) noexcept {
  return metadata_exact(cards.occurrence.metadata) && metadata_exact(cards.composition.metadata) &&
      metadata_exact(cards.receiver.metadata) && metadata_exact(cards.chart.metadata) &&
      metadata_exact(cards.conduct.metadata) && cards.occurrence.occurrence_count == 6 &&
      cards.composition.case_count == 5 && cards.receiver.source_count == 6 &&
      cards.conduct.case_count == 8;
}
}  // namespace elementary_mount_detail

HOLONICS_CALLABLE inline resident_elementary_calculus::resident_elementary_calculus(
    const organ::elementary_development_bundle &cards,
    const cultivated_organ_rest_record &record, cultivated_organ_remount_receipt &receipt) noexcept
    : standing_(record), cards_(cards),
      body_(body::continuing_body::remount(record.standing.body, receipt.body)) {
  const bool exact = record.integrity == cultivated_organ_rest_integrity(record);
  bool organs = true;
  for (std::uint8_t i = 0; i < organ::cultivation_family_count; ++i)
    organs = organs && record.organs[i].checker_founded &&
        record.organs[i].identity == exact::word{198'300U+i};
  receipt.first_organ = record.organs[0].identity; receipt.application = record.application.identity;
  receipt.same_body = exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.organs_preserved = exact && organs;
  receipt.application_preserved = record.applied && record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.organs_preserved && receipt.application_preserved &&
      !receipt.source_replayed && elementary_mount_detail::valid(cards);
  standing_.standing.body = {}; standing_.standing.integrity = 0; standing_.integrity = 0;
}

HOLONICS_CALLABLE inline resident_elementary_calculus::resident_elementary_calculus(
    const elementary_calculus_rest_record &record,
    elementary_calculus_remount_receipt &receipt) noexcept
    : standing_(record.standing), body_(body::continuing_body::remount(
          record.standing.standing.body,receipt.body)), laws_(record.laws),
      application_(record.application), calculus_morphology_(record.calculus_morphology),
      self_organ_morphology_(record.self_organ_morphology),
      derivation_morphology_(record.derivation_morphology),
      stage_(record.applied ? stage::applied : stage::derived) {
  const bool exact = record.integrity == elementary_calculus_rest_integrity(record);
  bool fibers = record.laws.checker_founded && record.laws.self_organ.checker_founded &&
      record.laws.self_organ.identity == exact::word{199'305};
  for (std::uint8_t i = 0; i < 6; ++i)
    fibers = fibers && record.laws.fibers[i].accepted &&
        record.laws.fibers[i].identity == exact::word{199'300U+i};
  receipt.first_fiber = record.laws.fibers[0].identity;
  receipt.self_organ = record.laws.self_organ.identity; receipt.application = record.application.identity;
  receipt.same_body = exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.prior_returns_preserved = record.standing.application.accepted;
  receipt.laws_preserved = exact && fibers;
  receipt.application_preserved = !record.applied || record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.prior_returns_preserved && receipt.laws_preserved &&
      receipt.application_preserved && !receipt.source_replayed;
  standing_.standing.body = {}; standing_.standing.integrity = 0; standing_.integrity = 0;
}

}  // namespace holonics::event
