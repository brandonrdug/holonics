#include "r4_verify.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

[[nodiscard]] bool same_observation(
    const event::body_observation& left,
    const event::body_observation& right) noexcept {
  if (left.head != right.head || left.continuation != right.continuation ||
      left.lineage != right.lineage) { return false; }
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    if (left.regions[slot].morphology != right.regions[slot].morphology ||
        left.regions[slot].current != right.regions[slot].current) { return false; }
  }
  return true;
}

}  // namespace

apparatus::body_lifecycle_input r4_input() noexcept {
  apparatus::body_lifecycle_input input{};
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    input.regions[slot].morphology = 10U * (slot + 1U);
    input.regions[slot].current = slot + 1U;
  }
  input.request = event::deed_request{200'000'000U, 2, 5};
  input.returned_payload = 7;
  return input;
}

std::size_t r4_verification_failures(
    const apparatus::body_lifecycle_input& input,
    const apparatus::body_lifecycle_executor_receipt& execution,
    const event::lifecycle_output& output) noexcept {
  std::size_t failures = execution.returned() ? 0 : 1;
  const std::uint64_t seed = input.request.owner_seed;
  if (output.predecessor.head != seed || output.predecessor.continuation != seed + 1'000'000U ||
      output.outbound.predecessor != seed || output.outbound.event != seed ||
      output.outbound.occurrence != seed + 1'000'000U ||
      output.outbound.outbound_port != seed + 2'000'000U ||
      output.outbound.expected_return_port != seed + 2'000'001U ||
      output.outbound.lineage != seed + 3'000'000U ||
      output.outbound.payload != input.request.payload ||
      output.outbound.region != input.request.region ||
      output.resume_state != event::lifecycle_status::exact ||
      output.commit.state != body::body_change_status::committed ||
      output.commit.predecessor.value() != seed || output.commit.successor.value() != seed + 1U ||
      output.commit.morphology_before != input.regions[input.request.region].morphology ||
      output.commit.morphology_after !=
          input.regions[input.request.region].morphology + input.returned_payload) {
    ++failures;
  }
  const std::uint64_t support = std::uint64_t{1} << input.request.region;
  if (output.delta.predecessor != seed || output.delta.input_event != seed ||
      output.delta.return_event != seed || output.delta.read_support != support ||
      output.delta.change_support != support || output.delta.incidence_delta != 0 ||
      output.delta.morphology_delta != input.returned_payload ||
      output.delta.successor_current != input.returned_payload ||
      output.delta.returned_consequence != input.returned_payload ||
      output.delta.stress != input.returned_payload || output.delta.obstruction != 0 ||
      output.delta.logical_resource != 1 || output.delta.lineage != seed + 3'000'001U ||
      output.delta.region != input.request.region) {
    ++failures;
  }
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    const std::uint64_t expected_morphology = input.regions[slot].morphology +
        (slot == input.request.region ? input.returned_payload : 0U);
    const std::uint64_t expected_current = slot == input.request.region
        ? input.returned_payload : input.regions[slot].current;
    if (output.successor.regions[slot].morphology != expected_morphology ||
        output.successor.regions[slot].current != expected_current) { ++failures; }
  }
  if (output.successor.head != seed + 1U ||
      output.successor.continuation != seed + 1'000'001U ||
      output.successor.lineage != seed + 2'000'001U || !output.rest.returned ||
      !output.rest.integrity_exact || !output.remount.returned || !output.remount.integrity_exact ||
      output.remount.source_replay_count != 0 || output.source_replays != 0 ||
      !same_observation(output.successor, output.remounted) || output.exterior_returns != 1) {
    ++failures;
  }
  const auto& adversarial = output.adversarial;
  if (adversarial.second_open != event::lifecycle_status::continuation_unavailable ||
      adversarial.foreign_return != event::lifecycle_status::foreign_return ||
      adversarial.stale_return != event::lifecycle_status::stale_return ||
      adversarial.correct_return != event::lifecycle_status::exact ||
      adversarial.double_return != event::lifecycle_status::already_resumed ||
      adversarial.capacity_commit != body::body_change_status::capacity_refused ||
      !adversarial.capacity_predecessor_preserved ||
      !adversarial.capacity_capability_restored ||
      !adversarial.interruption_predecessors[0] ||
      !adversarial.interruption_predecessors[1] ||
      !adversarial.interruption_predecessors[2] ||
      !adversarial.interruption_successor) {
    ++failures;
  }
  return failures;
}

}  // namespace holonics::tests
