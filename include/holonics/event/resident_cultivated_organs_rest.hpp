#pragma once

#include <holonics/event/resident_cultivated_organs.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline cultivated_organ_rest_receipt
resident_cultivated_organs::rest(cultivated_organ_rest_record &record) noexcept {
  cultivated_organ_rest_receipt receipt{};
  if (!admitted_ || pending_live_ || stage_ == stage::developmental) return receipt;
  record.standing = standing_; receipt.body = body_.rest(record.standing.body);
  if (!receipt.body.returned) return receipt;
  record.standing.integrity = rederivation_rest_integrity(record.standing);
  for (std::uint8_t i = 0; i < organ::cultivation_family_count; ++i)
    record.organs[i] = organs_[i];
  record.application = application_; record.cultivation_admitted_tally = cultivation_admitted_tally_;
  record.organ_admitted_tally = organ_admitted_tally_;
  record.application_admitted_tally = application_admitted_tally_;
  record.applied = stage_ == stage::applied;
  record.integrity = cultivated_organ_rest_integrity(record);
  receipt.first_organ = organs_[0].identity; receipt.application = application_.identity;
  receipt.integrity = exact::word{record.integrity};
  receipt.prior_returns_preserved = record.standing.matching_rederivation.accepted &&
      record.standing.lattice_rederivation.accepted &&
      record.standing.potential_rederivation.accepted &&
      record.standing.cover_rederivation.accepted;
  receipt.samples_absent = true; receipt.source_detached = true; receipt.returned = true;
  return receipt;
}

}  // namespace holonics::event
