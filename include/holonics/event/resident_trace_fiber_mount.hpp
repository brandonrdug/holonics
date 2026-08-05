#pragma once

#include <holonics/event/resident_trace_fiber.hpp>
#include <holonics/organ/characteristic_matrix_law.hpp>

namespace holonics::event {
namespace trace_fiber_mount_detail {
[[nodiscard]] HOLONICS_CALLABLE inline bool metadata(
    const organ::cultivation_card_metadata &m) noexcept {
  return m.parsed && m.schema.value() != 0 && m.occurrence.value() != 0 &&
         m.incoming_port.value() != 0 && m.return_port.value() != 0 &&
         m.lineage.value() != 0;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool valid(
    const organ::three_face_development_bundle &cards) noexcept {
  bool exact = true;
  for (const auto &source : cards.sources) {
    const auto &card = source.transitions;
    exact = exact && metadata(card.metadata) &&
            source.admitted_words == organ::trace_fiber_word_count &&
            card.alphabet_size >= 2 && card.alphabet_size <= 4 &&
            card.maximum_length >= 3 && card.maximum_length <= 4 &&
            organ::elementary_matrix_detail::determinant(card.rechart) == 1;
    for (std::uint8_t i = 0; i < card.alphabet_size; ++i)
      exact = exact &&
              organ::elementary_matrix_detail::determinant(card.generators[i]) == 1;
  }
  return exact;
}
} // namespace trace_fiber_mount_detail
HOLONICS_CALLABLE inline resident_trace_fiber::resident_trace_fiber(
    const organ::three_face_development_bundle &cards,
    const characteristic_hypergeometry_rest_record &record,
    hypergeometry_remount_receipt &receipt) noexcept
    : standing_(record), cards_(cards),
      body_(body::continuing_body::remount(
          record.standing.standing.standing.body, receipt.body)) {
  const bool exact = record.integrity == characteristic_rest_integrity(record);
  receipt.discovery = record.law.discovery.identity;
  receipt.organ = record.law.organ.identity;
  receipt.application = record.application.identity;
  receipt.same_body = exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.prior_returns_preserved =
      record.standing.applied && record.standing.application.accepted;
  receipt.law_preserved = record.law.checker_founded &&
                          record.law.organ.checker_founded;
  receipt.application_preserved = record.applied && record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.prior_returns_preserved &&
              receipt.law_preserved && receipt.application_preserved &&
              !receipt.source_replayed && trace_fiber_mount_detail::valid(cards);
  standing_.standing.standing.standing.body = {};
  standing_.standing.standing.standing.integrity = 0;
  standing_.standing.standing.integrity = 0;
  standing_.standing.integrity = 0;
  standing_.integrity = 0;
}
HOLONICS_CALLABLE inline resident_trace_fiber::resident_trace_fiber(
    const trace_fiber_rest_record &record,
    trace_fiber_remount_receipt &receipt) noexcept
    : standing_(record.standing),
      body_(body::continuing_body::remount(
          record.standing.standing.standing.standing.body, receipt.body)),
      law_(record.law), application_(record.application),
      trace_fiber_morphology_(record.trace_fiber_morphology),
      lift_organ_morphology_(record.lift_organ_morphology),
      triple_transport_morphology_(record.triple_transport_morphology),
      stage_(record.applied ? stage::applied : stage::derived) {
  const bool exact = record.integrity == trace_fiber_rest_integrity(record);
  receipt.discovery = record.law.discovery.identity;
  receipt.sum_organ = record.law.organs[0].identity;
  receipt.product_organ = record.law.organs[1].identity;
  receipt.application = record.application.identity;
  receipt.same_body = exact && receipt.body.returned && receipt.body.head == body_.head();
  receipt.prior_returns_preserved = record.standing.applied &&
                                    record.standing.application.accepted;
  receipt.laws_preserved = record.law.checker_founded &&
      record.law.discovery.accepted && record.law.discovery.identity == exact::word{201'300} &&
      record.law.organs[0].checker_founded && record.law.organs[0].identity == exact::word{201'301} &&
      record.law.organs[1].checker_founded && record.law.organs[1].identity == exact::word{201'302};
  receipt.application_preserved = !record.applied || record.application.accepted;
  receipt.source_replayed = receipt.body.source_replay_count != 0;
  admitted_ = receipt.same_body && receipt.prior_returns_preserved &&
              receipt.laws_preserved && receipt.application_preserved &&
              !receipt.source_replayed;
  standing_.standing.standing.standing.body = {};
  standing_.standing.standing.standing.integrity = 0;
  standing_.standing.standing.integrity = 0;
  standing_.standing.integrity = 0;
  standing_.integrity = 0;
}

} // namespace holonics::event
