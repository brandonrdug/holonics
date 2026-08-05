#pragma once

#include <type_traits>

#include <holonics/event/rederivation_rest.hpp>
#include <holonics/organ/cultivated_organ_receipt.hpp>

namespace holonics::event {

struct cultivated_organ_rest_record final {
  rederivation_rest_record standing{};
  organ::cultivated_shift_organ organs[organ::cultivation_family_count]{};
  organ::acquired_organ_application application{};
  std::uint64_t cultivation_morphology{};
  std::uint64_t organ_morphology{};
  std::uint64_t application_morphology{};
  std::uint64_t integrity{};
  bool applied{};
};

struct cultivated_organ_rest_receipt final {
  body::rest_receipt body{};
  exact::word first_organ{};
  exact::word application{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool samples_absent{};
  bool source_detached{};
  bool returned{};
};

struct cultivated_organ_remount_receipt final {
  body::rest_receipt body{};
  exact::word first_organ{};
  exact::word application{};
  bool same_body{};
  bool organs_preserved{};
  bool application_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE inline std::uint64_t
cultivated_organ_rest_integrity(const cultivated_organ_rest_record &record) noexcept {
  std::uint64_t fold = rederivation_rest_integrity(record.standing);
  for (const auto &organ : record.organs) {
    const std::uint64_t header[10]{organ.identity.value(), organ.passage.value(),
        organ.returned_event.value(), organ.lineage.value(), organ.order, organ.degree,
        organ.features, organ.minimum_prefix, static_cast<std::uint8_t>(organ.family),
        organ.checker_founded ? 1U : 0U};
    for (const auto value : header) terminal_rest_detail::fold_value(fold, value);
    for (std::uint8_t i = 0; i < organ.features; ++i)
      terminal_rest_detail::fold_value(fold, static_cast<std::uint64_t>(organ.coefficients[i]));
  }
  const std::uint64_t values[10]{record.application.identity.value(),
      record.application.passage.value(), record.application.returned_event.value(),
      record.application.lineage.value(), record.application.morphology_delta.value(),
      record.application.accepted ? 1U : 0U, record.cultivation_morphology,
      record.organ_morphology, record.application_morphology, record.applied ? 1U : 0U};
  for (const auto value : values) terminal_rest_detail::fold_value(fold, value);
  return fold;
}

static_assert(std::is_trivially_copyable_v<cultivated_organ_rest_record>);

}  // namespace holonics::event
