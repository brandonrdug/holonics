#pragma once

#include <holonics/event/resident_cultivated_organs.hpp>

namespace holonics::event {
namespace cultivated_mount_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool valid_card(
    const organ::developmental_stream_card &card) noexcept {
  if (!card.metadata.parsed || card.metadata.schema.value() == 0 ||
      card.metadata.occurrence.value() == 0 || card.metadata.incoming_port.value() == 0 ||
      card.metadata.return_port.value() == 0 || card.metadata.lineage.value() == 0 ||
      card.series_count == 0 || card.series_count > organ::cultivation_series_capacity ||
      card.maximum_order != 3 || card.maximum_degree != 2) return false;
  for (std::uint8_t series = 0; series < card.series_count; ++series)
    if (card.sample_count[series] == 0 ||
        card.sample_count[series] > organ::cultivation_sample_capacity) return false;
  return true;
}
}  // namespace cultivated_mount_detail

HOLONICS_CALLABLE inline resident_cultivated_organs::resident_cultivated_organs(
    const organ::developmental_stream_card (&cards)[organ::cultivation_family_count],
    const rederivation_rest_record &record, rederivation_remount_receipt &receipt) noexcept
    : standing_(record), body_(body::continuing_body::remount(record.body, receipt.body)) {
  const bool exact = record.integrity == rederivation_rest_integrity(record);
  admitted_ = exact && receipt.body.returned && record.cover_rederivation.accepted;
  for (std::uint8_t i = 0; i < organ::cultivation_family_count; ++i) {
    cards_[i] = cards[i]; admitted_ = admitted_ && cultivated_mount_detail::valid_card(cards[i]) &&
        static_cast<std::uint8_t>(cards[i].family) == i;
  }
  receipt.theory = record.matching_rederivation.identity;
  receipt.same_body = receipt.body.returned && receipt.body.head == body_.head();
  receipt.theory_preserved = exact && record.matching_rederivation.accepted &&
      record.lattice_rederivation.accepted && record.potential_rederivation.accepted &&
      record.cover_rederivation.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = admitted_ && receipt.same_body && receipt.theory_preserved;
  standing_.body = {}; standing_.integrity = 0;
}

HOLONICS_CALLABLE inline resident_cultivated_organs::resident_cultivated_organs(
    const cultivated_organ_rest_record &record,
    cultivated_organ_remount_receipt &receipt) noexcept
    : standing_(record.standing),
      body_(body::continuing_body::remount(record.standing.body, receipt.body)),
      application_(record.application), cultivation_morphology_(record.cultivation_morphology),
      organ_morphology_(record.organ_morphology),
      application_morphology_(record.application_morphology),
      stage_(record.applied ? stage::applied : stage::cultivated) {
  const bool exact = record.integrity == cultivated_organ_rest_integrity(record);
  bool organs_exact = true;
  for (std::uint8_t i = 0; i < organ::cultivation_family_count; ++i) {
    organs_[i] = record.organs[i]; organs_exact = organs_exact && organs_[i].checker_founded &&
        organs_[i].identity == exact::word{198'300U + i};
  }
  receipt.first_organ = organs_[0].identity; receipt.application = application_.identity;
  receipt.same_body = exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.organs_preserved = exact && organs_exact;
  receipt.application_preserved = !record.applied || application_.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.organs_preserved &&
      receipt.application_preserved && !receipt.source_replayed;
  standing_.body = {}; standing_.integrity = 0;
}

}  // namespace holonics::event
