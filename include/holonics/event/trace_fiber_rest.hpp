#pragma once

#include <type_traits>

#include <holonics/event/characteristic_hypergeometry_rest.hpp>
#include <holonics/organ/heldout_trace_fiber_law.hpp>

namespace holonics::event {

struct acquired_trace_fiber final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};
struct trace_fiber_law_bundle final {
  acquired_trace_fiber discovery{};
  organ::trace_fiber_organ organs[2]{};
  std::uint16_t triple_count[3]{};
  std::uint16_t group_count{};
  std::uint16_t branch_count{};
  std::uint16_t two_sheet_count{};
  bool checker_founded{};
};
struct trace_fiber_application final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};
struct trace_fiber_rest_record final {
  characteristic_hypergeometry_rest_record standing{};
  trace_fiber_law_bundle law{};
  trace_fiber_application application{};
  std::uint64_t trace_fiber_admitted_tally{};
  std::uint64_t lift_organ_admitted_tally{};
  std::uint64_t triple_transport_admitted_tally{};
  std::uint64_t integrity{};
  bool applied{};
};
struct trace_fiber_rest_receipt final {
  body::rest_receipt body{};
  exact::word discovery{};
  exact::word sum_organ{};
  exact::word product_organ{};
  exact::word application{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool developmental_rows_absent{};
  bool target_traces_absent{};
  bool matrices_absent{};
  bool source_detached{};
  bool returned{};
};
struct trace_fiber_remount_receipt final {
  body::rest_receipt body{};
  exact::word discovery{};
  exact::word sum_organ{};
  exact::word product_organ{};
  exact::word application{};
  bool same_body{};
  bool prior_returns_preserved{};
  bool laws_preserved{};
  bool application_preserved{};
  bool source_replayed{};
};
[[nodiscard]] HOLONICS_CALLABLE inline std::uint64_t
trace_fiber_rest_integrity(const trace_fiber_rest_record &r) noexcept {
  std::uint64_t fold = characteristic_rest_integrity(r.standing);
  const std::uint64_t first[8]{
      r.law.discovery.identity.value(), r.law.discovery.passage.value(),
      r.law.discovery.returned_event.value(), r.law.discovery.lineage.value(),
      r.law.discovery.admitted_tally_delta.value(), r.law.discovery.accepted ? 1U : 0U,
      r.law.group_count, r.law.checker_founded ? 1U : 0U};
  for (const auto value : first)
    terminal_rest_detail::fold_value(fold, value);
  for (const auto value : r.law.triple_count)
    terminal_rest_detail::fold_value(fold, value);
  terminal_rest_detail::fold_value(fold, r.law.branch_count);
  terminal_rest_detail::fold_value(fold, r.law.two_sheet_count);
  for (const auto &organ : r.law.organs) {
    const std::uint64_t head[7]{
        organ.identity.value(), organ.passage.value(), organ.returned_event.value(),
        organ.lineage.value(), static_cast<std::uint8_t>(organ.target),
        organ.primitive ? 1U : 0U, organ.checker_founded ? 1U : 0U};
    for (const auto value : head)
      terminal_rest_detail::fold_value(fold, value);
    for (const auto value : organ.coefficients)
      terminal_rest_detail::fold_value(fold, static_cast<std::uint64_t>(value));
  }
  const std::uint64_t tail[12]{
      r.application.identity.value(), r.application.passage.value(),
      r.application.returned_event.value(), r.application.lineage.value(),
      r.application.admitted_tally_delta.value(), r.application.accepted ? 1U : 0U,
      r.trace_fiber_admitted_tally, r.lift_organ_admitted_tally,
      r.triple_transport_admitted_tally, r.applied ? 1U : 0U,
      r.standing.characteristic_admitted_tally, r.standing.trace_organ_admitted_tally};
  for (const auto value : tail)
    terminal_rest_detail::fold_value(fold, value);
  return fold;
}
static_assert(std::is_trivially_copyable_v<trace_fiber_rest_record>);

} // namespace holonics::event
