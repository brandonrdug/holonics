#include <cstddef>
#include <cstdint>
#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/body_lifecycle_resident.hpp>

namespace holonics::apparatus {
namespace {
template<class Value>
struct local_slot final {
  alignas(Value) unsigned char bytes[sizeof(Value)];
  [[nodiscard]] __device__ Value* get() { return reinterpret_cast<Value*>(bytes); }
};

[[nodiscard]] __device__ bool same_observation(
    const event::body_observation& left,
    const event::body_observation& right) {
  if (left.head != right.head || left.continuation != right.continuation ||
      left.lineage != right.lineage) { return false; }
  for (std::size_t slot = 0; slot < body::live_region_capacity; ++slot) {
    if (left.regions[slot].current != right.regions[slot].current) { return false; }
  }
  return true;
}

[[nodiscard]] __device__ event::deed_return matching_return(
    const event::outbound_occurrence& outbound,
    std::uint64_t payload) {
  return event::deed_return{outbound.predecessor, outbound.event,
      outbound.expected_return_port, outbound.lineage + 1U, payload};
}

__device__ void check_returns(event::lifecycle_adversarial_receipt& receipt) {
  body::rest_region regions[body::live_region_capacity]{};
  local_slot<body::continuing_body> body_storage{};
  local_slot<event::live_pending> pending_storage{};
  local_slot<event::live_pending> second_pending_storage{};
  local_slot<event::live_delta> delta_storage{};
  auto* standing = ::new (static_cast<void*>(body_storage.get()))
      body::continuing_body{40'000'000U, regions};
  const event::deed_request request{50'000'000U, 1, 3};
  event::outbound_occurrence outbound{};
  static_cast<void>(event::open(*standing, request, pending_storage.get(), outbound));
  event::outbound_occurrence second_outbound{};
  receipt.second_open = event::open(
      *standing, request, second_pending_storage.get(), second_outbound);
  auto returned = matching_return(outbound, 7);
  returned.event += 1U;
  receipt.foreign_return = event::resume(*pending_storage.get(), returned, delta_storage.get());
  returned = matching_return(outbound, 7);
  returned.predecessor += 1U;
  receipt.stale_return = event::resume(*pending_storage.get(), returned, delta_storage.get());
  returned = matching_return(outbound, 7);
  receipt.correct_return = event::resume(*pending_storage.get(), returned, delta_storage.get());
  receipt.double_return = event::resume(*pending_storage.get(), returned, delta_storage.get());
  event::recover(*standing, *delta_storage.get());
}

__device__ bool recover_open_boundary(std::uint64_t seed) {
  body::rest_region regions[body::live_region_capacity]{};
  local_slot<body::continuing_body> body_storage{};
  local_slot<event::live_pending> pending_storage{};
  auto* standing = ::new (static_cast<void*>(body_storage.get()))
      body::continuing_body{seed, regions};
  const auto before = event::observe(*standing);
  const event::deed_request request{seed + 10'000'000U, 1, 3};
  event::outbound_occurrence outbound{};
  static_cast<void>(event::open(*standing, request, pending_storage.get(), outbound));
  event::recover(*standing, *pending_storage.get());
  return same_observation(before, event::observe(*standing));
}

__device__ bool recover_resume_boundary(std::uint64_t seed) {
  body::rest_region regions[body::live_region_capacity]{};
  local_slot<body::continuing_body> body_storage{};
  local_slot<event::live_pending> pending_storage{};
  local_slot<event::live_delta> delta_storage{};
  auto* standing = ::new (static_cast<void*>(body_storage.get()))
      body::continuing_body{seed, regions};
  const auto before = event::observe(*standing);
  const event::deed_request request{seed + 10'000'000U, 1, 3};
  event::outbound_occurrence outbound{};
  static_cast<void>(event::open(*standing, request, pending_storage.get(), outbound));
  auto returned = matching_return(outbound, 7);
  static_cast<void>(event::resume(*pending_storage.get(), returned, delta_storage.get()));
  event::recover(*standing, *delta_storage.get());
  return same_observation(before, event::observe(*standing));
}

__device__ bool rest_predecessor_boundary(std::uint64_t seed) {
  body::rest_region regions[body::live_region_capacity]{};
  local_slot<body::continuing_body> body_storage{};
  local_slot<body::continuing_body> remount_storage{};
  body::rest_record rest{};
  body::rest_receipt rest_receipt{};
  auto* standing = ::new (static_cast<void*>(body_storage.get()))
      body::continuing_body{seed, regions};
  const auto before = event::observe(*standing);
  static_cast<void>(standing->rest(rest));
  auto* remounted = ::new (static_cast<void*>(remount_storage.get()))
      body::continuing_body{body::continuing_body::remount(rest, rest_receipt)};
  return rest_receipt.returned && same_observation(before, event::observe(*remounted));
}

__device__ bool commit_successor_boundary(std::uint64_t seed) {
  body::rest_region regions[body::live_region_capacity]{};
  local_slot<body::continuing_body> body_storage{};
  local_slot<event::live_pending> pending_storage{};
  local_slot<event::live_delta> delta_storage{};
  auto* standing = ::new (static_cast<void*>(body_storage.get()))
      body::continuing_body{seed, regions};
  const event::deed_request request{seed + 10'000'000U, 1, 3};
  event::outbound_occurrence outbound{};
  static_cast<void>(event::open(*standing, request, pending_storage.get(), outbound));
  auto returned = matching_return(outbound, 7);
  static_cast<void>(event::resume(*pending_storage.get(), returned, delta_storage.get()));
  const auto committed = event::commit(*standing, *delta_storage.get());
  // The commit's effect is structural, not arithmetic: the head advances to a
  // freshly minted identity and a new continuation stands where the consumed one
  // was. This read `region(1).admitted_tally == 7` until 2026-08-07, which
  // checked that a counter had been added to and said nothing about the change.
  return committed.state == body::body_change_status::committed &&
      committed.successor != committed.predecessor &&
      committed.continuation_after != committed.continuation_before &&
      standing->can_open();
}

__global__ void adversarial_lifecycle(event::lifecycle_output* output) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  auto& receipt = output->adversarial;
  check_returns(receipt);
  receipt.interruption_predecessors[0] = rest_predecessor_boundary(80'000'000U);
  receipt.interruption_predecessors[1] = recover_open_boundary(90'000'000U);
  receipt.interruption_predecessors[2] = recover_resume_boundary(100'000'000U);
  receipt.interruption_successor = commit_successor_boundary(110'000'000U);
}

}  // namespace

cudaError_t launch_body_adversarial(event::lifecycle_output* output) noexcept {
  adversarial_lifecycle<<<1, 1>>>(output);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
