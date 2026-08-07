#pragma once

#include <type_traits>

#include <holonics/event/trace_fiber_rest.hpp>
#include <holonics/organ/trace_rebase_receipt.hpp>

namespace holonics::event {
struct acquired_trace_rebase final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  bool accepted{};
};
struct trace_rebase_deck_organ final {
  acquired_trace_rebase return_receipt{};
  std::int64_t vector[organ::trace_rebase_coordinate_count]{};
  std::int64_t image[organ::trace_rebase_coordinate_count]{};
  std::int64_t eigenvalue{};
  bool primitive{};
};
struct trace_rebase_law_bundle final {
  acquired_trace_rebase discovery{};
  organ::trace_rebase_map_organ maps[organ::trace_rebase_move_count]{};
  acquired_trace_rebase tangent{};
  trace_rebase_deck_organ deck{};
  organ::trace_rebase_counts transitions[organ::trace_rebase_move_count]{};
  bool checker_founded{};
};
struct trace_rebase_application final {
  exact::word identity{};
  exact::word passage{};
  exact::word returned_event{};
  exact::word lineage{};
  bool accepted{};
};
struct trace_rebase_rest_record final {
  trace_fiber_rest_record standing{};
  trace_rebase_law_bundle law{};
  trace_rebase_application application{};
  std::uint64_t integrity{};
  bool applied{};
};
struct trace_rebase_rest_receipt final {
  body::rest_receipt body{};
  exact::word discovery{};
  exact::word tangent{};
  exact::word deck{};
  exact::word application{};
  exact::word integrity{};
  bool prior_returns_preserved{};
  bool developmental_rows_absent{};
  bool matrices_absent{};
  bool tangent_rows_absent{};
  bool source_detached{};
  bool returned{};
};
struct trace_rebase_remount_receipt final {
  body::rest_receipt body{};
  exact::word discovery{};
  exact::word tangent{};
  exact::word deck{};
  exact::word application{};
  bool same_body{};
  bool prior_returns_preserved{};
  bool maps_preserved{};
  bool differential_preserved{};
  bool application_preserved{};
  bool source_replayed{};
};
[[nodiscard]] HOLONICS_CALLABLE inline std::uint64_t
trace_rebase_rest_integrity(const trace_rebase_rest_record &r) noexcept {
  std::uint64_t fold = trace_fiber_rest_integrity(r.standing);
  const std::uint64_t first[8]{
      r.law.discovery.identity.value(), r.law.discovery.passage.value(),
      r.law.discovery.returned_event.value(), r.law.discovery.lineage.value(), r.law.discovery.accepted ? 1U : 0U,
      r.law.tangent.identity.value(),
      r.law.deck.return_receipt.identity.value(),
      r.law.checker_founded ? 1U : 0U};
  for (const auto value : first)
    terminal_rest_detail::fold_value(fold, value);
  for (const auto &map : r.law.maps) {
    const std::uint64_t head[7]{
        map.identity.value(), map.passage.value(), map.returned_event.value(),
        map.lineage.value(), static_cast<std::uint8_t>(map.move),
        map.primitive ? 1U : 0U, map.checker_founded ? 1U : 0U};
    for (const auto value : head)
      terminal_rest_detail::fold_value(fold, value);
    for (const auto degree : map.degrees)
      terminal_rest_detail::fold_value(fold, degree);
    for (const auto &coordinate : map.coefficients)
      for (const auto coefficient : coordinate)
        terminal_rest_detail::fold_value(
            fold, static_cast<std::uint64_t>(coefficient));
  }
  for (const auto &count : r.law.transitions) {
    terminal_rest_detail::fold_value(fold, count.regular_regular);
    terminal_rest_detail::fold_value(fold, count.regular_branch);
    terminal_rest_detail::fold_value(fold, count.branch_regular);
    terminal_rest_detail::fold_value(fold, count.branch_branch);
  }
  for (const auto value : r.law.deck.vector)
    terminal_rest_detail::fold_value(fold, static_cast<std::uint64_t>(value));
  for (const auto value : r.law.deck.image)
    terminal_rest_detail::fold_value(fold, static_cast<std::uint64_t>(value));
  terminal_rest_detail::fold_value(
      fold, static_cast<std::uint64_t>(r.law.deck.eigenvalue));
  terminal_rest_detail::fold_value(fold, r.law.deck.primitive ? 1U : 0U);
  const std::uint64_t tail[7]{
      r.application.identity.value(), r.application.passage.value(),
      r.application.returned_event.value(), r.application.lineage.value(), r.application.accepted ? 1U : 0U,
      r.applied ? 1U : 0U,
      r.law.tangent.accepted && r.law.deck.return_receipt.accepted ? 1U : 0U};
  for (const auto value : tail)
    terminal_rest_detail::fold_value(fold, value);
  return fold;
}
static_assert(std::is_trivially_copyable_v<trace_rebase_rest_record>);

} // namespace holonics::event
