#pragma once

#include <type_traits>

#include <holonics/event/cultivated_organ_rest.hpp>
#include <holonics/organ/elementary_calculus_receipt.hpp>

namespace holonics::event {
struct acquired_elementary_fiber final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  bool accepted{};
};

struct elementary_law_bundle final {
  acquired_elementary_fiber fibers[6]{};
  organ::cultivated_shift_organ self_organ{};
  organ::exact_matrix2 path_residual{};
  organ::exact_matrix2 closed_word{};
  std::uint8_t composition_codes[5]{};
  std::uint8_t conduct_conditions[7]{};
  std::uint16_t conduct_code{};
  std::uint8_t occurrence_mask{};
  std::uint8_t coarse_fibers{};
  std::uint8_t fine_fibers{};
  std::uint8_t strict_witnesses{};
  bool boundary_exact{};
  bool receiver_reopens{};
  bool curved{};
  bool conduct_exact{};
  bool checker_founded{};
};

struct elementary_application_fiber final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  bool accepted{};
};

struct elementary_calculus_rest_record final {
  cultivated_organ_rest_record standing{};
  elementary_law_bundle laws{};
  elementary_application_fiber application{};
  std::uint64_t integrity{};
  bool applied{};
};

struct elementary_calculus_rest_receipt final {
  body::rest_receipt body{};
  exact::word first_fiber{};
  exact::word self_organ{};
  exact::word application{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool development_rows_absent{};
  bool traces_absent{};
  bool source_detached{};
  bool returned{};
};

struct elementary_calculus_remount_receipt final {
  body::rest_receipt body{};
  exact::word first_fiber{};
  exact::word self_organ{};
  exact::word application{};
  bool same_body{};
  bool prior_returns_preserved{};
  bool laws_preserved{};
  bool application_preserved{};
  bool source_replayed{};
};

[[nodiscard]] HOLONICS_CALLABLE inline std::uint64_t elementary_calculus_rest_integrity(
    const elementary_calculus_rest_record &record) noexcept {
  std::uint64_t fold = cultivated_organ_rest_integrity(record.standing);
  for (const auto &fiber : record.laws.fibers) {
    const std::uint64_t values[5]{fiber.identity.value(),fiber.passage.value(),
        fiber.returned_event.value(),fiber.lineage.value(),
        fiber.accepted ? 1U : 0U};
    for (const auto value : values) terminal_rest_detail::fold_value(fold,value);
  }
  const auto &organ = record.laws.self_organ;
  const std::uint64_t organ_values[8]{organ.identity.value(),organ.passage.value(),
      organ.returned_event.value(),organ.lineage.value(),organ.order,organ.degree,
      organ.features,organ.checker_founded ? 1U : 0U};
  for (const auto value : organ_values) terminal_rest_detail::fold_value(fold,value);
  for (std::uint8_t i = 0; i < organ.features; ++i)
    terminal_rest_detail::fold_value(fold,static_cast<std::uint64_t>(organ.coefficients[i]));
  for (const auto value : record.laws.path_residual.value)
    terminal_rest_detail::fold_value(fold,static_cast<std::uint64_t>(value));
  for (const auto value : record.laws.closed_word.value)
    terminal_rest_detail::fold_value(fold,static_cast<std::uint64_t>(value));
  for (const auto value : record.laws.composition_codes)
    terminal_rest_detail::fold_value(fold,value);
  for (const auto value : record.laws.conduct_conditions)
    terminal_rest_detail::fold_value(fold,value);
  const std::uint64_t law_values[10]{record.laws.conduct_code,record.laws.occurrence_mask,
      record.laws.coarse_fibers,record.laws.fine_fibers,record.laws.strict_witnesses,
      record.laws.boundary_exact ? 1U : 0U,record.laws.receiver_reopens ? 1U : 0U,
      record.laws.curved ? 1U : 0U,record.laws.conduct_exact ? 1U : 0U,
      record.laws.checker_founded ? 1U : 0U};
  for (const auto value : law_values) terminal_rest_detail::fold_value(fold,value);
  const std::uint64_t tail[8]{record.application.identity.value(),record.application.passage.value(),
      record.application.returned_event.value(),record.application.lineage.value(),record.application.accepted ? 1U : 0U,
      record.laws.conduct_code,record.laws.occurrence_mask,record.applied ? 1U : 0U};
  for (const auto value : tail) terminal_rest_detail::fold_value(fold,value);
  return fold;
}

static_assert(std::is_trivially_copyable_v<elementary_calculus_rest_record>);

}  // namespace holonics::event
