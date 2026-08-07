#pragma once

#include <type_traits>

#include <holonics/event/elementary_calculus_rest.hpp>
#include <holonics/organ/characteristic_hypergeometry_receipt.hpp>

namespace holonics::event {
struct acquired_characteristic_fiber final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  bool accepted{};
};
struct characteristic_law_bundle final {
  acquired_characteristic_fiber discovery{};
  organ::trace_law_organ organ{};
  std::uint16_t pair_count[3]{};
  std::uint16_t group_count{};
  std::uint16_t closed_strata[3]{};
  bool checker_founded{};
};
struct characteristic_application_fiber final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  bool accepted{};
};
struct characteristic_hypergeometry_rest_record final {
  elementary_calculus_rest_record standing{};
  characteristic_law_bundle law{};
  characteristic_application_fiber application{};
  std::uint64_t integrity{};
  bool applied{};
};
struct hypergeometry_rest_receipt final {
  body::rest_receipt body{};
  exact::word discovery{};
  exact::word organ{};
  exact::word application{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool developmental_rows_absent{};
  bool matrices_absent{};
  bool source_detached{};
  bool returned{};
};
struct hypergeometry_remount_receipt final {
  body::rest_receipt body{};
  exact::word discovery{};
  exact::word organ{};
  exact::word application{};
  bool same_body{};
  bool prior_returns_preserved{};
  bool law_preserved{};
  bool application_preserved{};
  bool source_replayed{};
};
[[nodiscard]] HOLONICS_CALLABLE inline std::uint64_t
characteristic_rest_integrity(
    const characteristic_hypergeometry_rest_record &r) noexcept {
  std::uint64_t fold = elementary_calculus_rest_integrity(r.standing);
  const std::uint64_t first[6]{r.law.discovery.identity.value(),
                               r.law.discovery.passage.value(),
                               r.law.discovery.returned_event.value(),
                               r.law.discovery.lineage.value(),
                               r.law.discovery.accepted ? 1U : 0U,
                               r.law.group_count};
  for (const auto value : first)
    terminal_rest_detail::fold_value(fold, value);
  for (const auto value : r.law.pair_count)
    terminal_rest_detail::fold_value(fold, value);
  for (const auto value : r.law.closed_strata)
    terminal_rest_detail::fold_value(fold, value);
  const auto &o = r.law.organ;
  const std::uint64_t organ[7]{
      o.identity.value(),         o.passage.value(), o.returned_event.value(),
      o.lineage.value(),          o.features,        o.primitive ? 1U : 0U,
      o.checker_founded ? 1U : 0U};
  for (const auto value : organ)
    terminal_rest_detail::fold_value(fold, value);
  for (const auto value : o.coefficients)
    terminal_rest_detail::fold_value(fold, static_cast<std::uint64_t>(value));
  const std::uint64_t tail[7]{r.application.identity.value(),
                               r.application.passage.value(),
                               r.application.returned_event.value(),
                               r.application.lineage.value(),
                               r.application.accepted ? 1U : 0U,
                               r.law.checker_founded ? 1U : 0U,
                               r.applied ? 1U : 0U};
  for (const auto value : tail)
    terminal_rest_detail::fold_value(fold, value);
  return fold;
}
static_assert(
    std::is_trivially_copyable_v<characteristic_hypergeometry_rest_record>);

} // namespace holonics::event
