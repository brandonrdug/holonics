#pragma once

#include <cstddef>
#include <cstdint>
#include <new>

#include <holonics/body/continuing_body.hpp>
#include <holonics/event/live_delta.hpp>
#include <holonics/event/live_pending.hpp>
#include <holonics/structure/identity_mint.hpp>

namespace holonics::event {
[[nodiscard]] HOLONICS_CALLABLE inline body_observation observe(
    const body::continuing_body& standing) noexcept {
  body_observation result{};
  result.head = standing.head().value();
  result.continuation = standing.continuation_serial().value();
  result.lineage = standing.lineage().value();
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    result.regions[slot] = standing.region(slot);
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline lifecycle_status open(
    body::continuing_body& standing,
    const deed_request& request,
    live_pending* pending_storage,
    outbound_occurrence& outbound) noexcept {
  if (!standing.can_open() || pending_storage == nullptr || request.region >= body::live_region_capacity) {
    return lifecycle_status::continuation_unavailable;
  }
  structure::identity_mint<structure::event_identity_owner> event_mint{request.owner_seed};
  structure::identity_mint<structure::occurrence_identity_owner> occurrence_mint{
      request.owner_seed + 1'000'000U};
  structure::identity_mint<structure::port_identity_owner> port_mint{
      request.owner_seed + 2'000'000U};
  structure::identity_mint<structure::lineage_identity_owner> lineage_mint{
      request.owner_seed + 3'000'000U};
  outbound.predecessor = standing.head().value();
  outbound.event = event_mint.mint().serial().value();
  outbound.occurrence = occurrence_mint.mint().serial().value();
  outbound.outbound_port = port_mint.mint().serial().value();
  outbound.expected_return_port = port_mint.mint().serial().value();
  outbound.lineage = lineage_mint.mint().serial().value();
  outbound.payload = request.payload;
  outbound.region = request.region;
  ::new (static_cast<void*>(pending_storage)) live_pending{
      standing.take_continuation(), outbound};
  return lifecycle_status::exact;
}

[[nodiscard]] HOLONICS_CALLABLE inline lifecycle_status resume(
    live_pending& pending,
    const deed_return& returned,
    live_delta* delta_storage) noexcept {
  if (!pending.resumable()) { return lifecycle_status::already_resumed; }
  const auto& expected = pending.outbound();
  if (returned.predecessor != expected.predecessor) { return lifecycle_status::stale_return; }
  if (returned.event != expected.event) { return lifecycle_status::foreign_return; }
  if (returned.port != expected.expected_return_port) { return lifecycle_status::wrong_return_port; }
  if (returned.lineage != expected.lineage + 1U || delta_storage == nullptr) {
    return lifecycle_status::malformed_return;
  }
  const std::uint64_t support = std::uint64_t{1} << expected.region;
  complete_delta_receipt receipt{};
  receipt.predecessor = expected.predecessor;
  receipt.input_event = expected.event;
  receipt.return_event = returned.event;
  receipt.read_support = support;
  receipt.change_support = support;
  receipt.incidence_delta = 0;
  receipt.successor_current = returned.payload;
  receipt.returned_consequence = returned.payload;
  receipt.stress = returned.payload;
  receipt.obstruction = 0;
  receipt.logical_resource = 1;
  receipt.lineage = returned.lineage;
  receipt.region = expected.region;
  ::new (static_cast<void*>(delta_storage)) live_delta{
      pending.take_continuation(), receipt};
  return lifecycle_status::exact;
}

[[nodiscard]] HOLONICS_CALLABLE inline body::body_change_receipt commit(
    body::continuing_body& standing,
    live_delta& delta) noexcept {
  const auto receipt = delta.receipt();
  return standing.commit(exact::word{receipt.predecessor}, receipt.region, receipt.successor_current, delta.take_continuation());
}

HOLONICS_CALLABLE inline void recover(
    body::continuing_body& standing,
    live_pending& pending) noexcept {
  standing.recover(pending.take_continuation());
}

HOLONICS_CALLABLE inline void recover(
    body::continuing_body& standing,
    live_delta& delta) noexcept {
  standing.recover(delta.take_continuation());
}

}  // namespace holonics::event
