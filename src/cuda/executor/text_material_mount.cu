#include <cstdint>

#include "text_mount_query.cuh"

namespace holonics::apparatus {
namespace {

using codec::text_arena;
using organ::incidence_arena;
using organ::suffix_arena;
using text_mount::host_query;
using text_mount::release;
using text_mount::text_query_kernel;
using text_mount::text_query_return;
using text_mount::try_reserve;

}  // namespace

text_mount_receipt mount_text_material(text_mount_request request) noexcept {
  text_mount_receipt receipt{};
  if (request.sections == nullptr || request.section_count == 0 ||
      request.octet_aperture == 0 || request.query_paths == 0) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  static_cast<void>(cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0));
  static_cast<void>(cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0));
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);

  text_mount::text_host host{};
  text_arena remounted{};
  suffix_arena suffix{};
  incidence_arena incidence{};
  unsigned char* earlier = nullptr;
  unsigned char* later = nullptr;
  text_query_return* returns = nullptr;
  std::uint64_t octets = 0;
  const std::uint32_t rest_capacity = request.surface_capacity +
      (request.occurrence_capacity * codec::text_occurrence_octets) +
      (request.caused_capacity * 4U) + codec::text_rest_header_octets;
  const bool reserved =
      try_reserve(host.text.surface, request.surface_capacity, octets) &&
      try_reserve(host.text.occurrences, request.occurrence_capacity, octets) &&
      try_reserve(host.text.caused, request.caused_capacity, octets) &&
      try_reserve(remounted.surface, request.surface_capacity, octets) &&
      try_reserve(remounted.occurrences, request.occurrence_capacity, octets) &&
      try_reserve(remounted.caused, request.caused_capacity, octets) &&
      try_reserve(suffix.states, request.state_capacity, octets) &&
      try_reserve(suffix.transitions, request.transition_capacity, octets) &&
      try_reserve(suffix.next, request.transition_capacity, octets) &&
      try_reserve(incidence.staged, request.incidence_capacity, octets) &&
      try_reserve(incidence.staged_next, request.incidence_capacity, octets) &&
      try_reserve(incidence.ordered_sources, request.incidence_capacity, octets) &&
      try_reserve(incidence.spans, request.state_capacity, octets) &&
      try_reserve(incidence.direct_head, request.state_capacity, octets) &&
      try_reserve(incidence.first_child, request.state_capacity, octets) &&
      try_reserve(incidence.next_sibling, request.state_capacity, octets) &&
      try_reserve(incidence.walk_stack, request.state_capacity, octets) &&
      cudaMallocManaged(reinterpret_cast<void**>(&earlier), rest_capacity) ==
          cudaSuccess &&
      cudaMallocManaged(reinterpret_cast<void**>(&later), rest_capacity) == cudaSuccess &&
      cudaMallocManaged(reinterpret_cast<void**>(&returns),
          sizeof(text_query_return) * request.query_paths) == cudaSuccess;
  if (!reserved) {
    receipt.state = executor_status::allocation_refused;
    return receipt;
  }
  receipt.resident_octets = octets;
  receipt.frame_octets =
      sizeof(text_arena) + sizeof(suffix_arena) + sizeof(incidence_arena);

  for (std::uint32_t slot = 0; slot < request.section_count; ++slot) {
    static_cast<void>(text_mount::admit(host, request.sections[slot]));
  }
  receipt.containers = request.containers;
  receipt.occurrences = host.text.occurrences_used;
  receipt.surface_octets = host.text.surface_used;
  receipt.duplicate_witnesses = host.text.duplicate_witnesses;
  receipt.version_fibers = host.text.version_fibers;
  receipt.open_causal_fibers = host.text.open_causal_fibers;

  // A refused crossing consumes nothing and returns the exact predecessor.
  const auto refusal = text_mount::try_cross(host, false);
  receipt.refusal_returned_predecessor = refusal.predecessor_returned &&
      host.state == text_mount::host_state::standing;

  if (!organ::suffix_law::try_found_root(suffix) ||
      !organ::incidence_law::try_open(incidence)) {
    receipt.state = executor_status::allocation_refused;
    return receipt;
  }
  const auto conditioned = event::condition_text(
      host.text, suffix, incidence, request.octet_aperture);
  if (!conditioned.complete) {
    receipt.state = executor_status::invalid_aperture;
    return receipt;
  }
  receipt.states = conditioned.states;
  receipt.transitions = conditioned.transitions;
  receipt.caused_admitted = conditioned.caused_admitted;
  receipt.octets_crossed = conditioned.octets_crossed;
  receipt.global_pair_population = conditioned.pair_population;
  receipt.formation_steps = incidence.formation_steps;
  receipt.lookup_steps = suffix.lookup_steps;

  // The successful crossing consumes the host; it must then refuse admission.
  const auto crossed = text_mount::try_cross(host, true);
  receipt.mount_consumed_host =
      crossed.obstruction == executor_status::returned &&
      host.state == text_mount::host_state::consumed;
  receipt.consumed_host_refuses_admission =
      text_mount::admit(host, request.sections[0]) ==
      codec::text_admission::capacity_refused;

  receipt.rest_octets =
      codec::text_rest_law::encode(host.text, earlier, rest_capacity);
  receipt.remount_founded_from_octets_alone =
      codec::text_rest_law::decode(remounted, earlier, receipt.rest_octets);
  receipt.remount_exact = receipt.remount_founded_from_octets_alone &&
      text_mount::same_standing(host.text, remounted);

  // One emanated deed returns to the remounted body with its cause supplied.
  const unsigned char emanated[4] = {'e', 'r', 'o', 's'};
  const std::uint32_t cause = 0;
  static_cast<void>(codec::text_law::try_admit(remounted, request.containers + 1U, 0,
      codec::text_role::assistant, codec::text_phase::emanated, emanated, 4, &cause, 1));
  receipt.remount_octets = codec::text_rest_law::encode(remounted, later, rest_capacity);
  receipt.bounded_delta_equal = receipt.remount_octets != 0 &&
      codec::text_rest_law::append_stable(earlier, later);

  const std::uint64_t formation_before = incidence.formation_steps;
  const std::uint32_t block = 128;
  const std::uint32_t grid = (request.query_paths + (block - 1U)) >> 7U;
  text_query_kernel<<<grid, block>>>(
      host.text, suffix, incidence, request.query_paths, request.octet_aperture, returns);
  if (cudaGetLastError() != cudaSuccess) {
    receipt.state = executor_status::launch_refused;
    return receipt;
  }
  if (cudaDeviceSynchronize() != cudaSuccess) {
    receipt.state = executor_status::synchronization_refused;
    return receipt;
  }
  for (std::uint32_t slot = 0; slot < request.query_paths; ++slot) {
    const auto expected =
        host_query(host.text, suffix, incidence, slot, request.octet_aperture);
    if (returns[slot].state != expected.state ||
        returns[slot].matched != expected.matched ||
        returns[slot].span_length != expected.span_length ||
        returns[slot].reaches_own != expected.reaches_own) {
      receipt.parity_failures = receipt.parity_failures + 1U;
    }
  }
  receipt.device_queries = request.query_paths;
  receipt.hot_host_replay_work = incidence.formation_steps - formation_before;
  receipt.state = executor_status::returned;

  release(host.text.surface.first);
  release(host.text.occurrences.first);
  release(host.text.caused.first);
  release(remounted.surface.first);
  release(remounted.occurrences.first);
  release(remounted.caused.first);
  release(suffix.states.first);
  release(suffix.transitions.first);
  release(suffix.next.first);
  release(incidence.staged.first);
  release(incidence.staged_next.first);
  release(incidence.ordered_sources.first);
  release(incidence.spans.first);
  release(incidence.direct_head.first);
  release(incidence.first_child.first);
  release(incidence.next_sibling.first);
  release(incidence.walk_stack.first);
  release(earlier);
  release(later);
  release(returns);
  return receipt;
}

}  // namespace holonics::apparatus
