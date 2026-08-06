#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/resident_ecology_executor.hpp>
#include <holonics/organ/suffix_extend.hpp>

namespace holonics::apparatus {
namespace {

using organ::incidence_arena;
using organ::no_state;
using organ::source_span;
using organ::suffix_arena;
using organ::suffix_symbol;

/// One answered query. The card returns the reached state, the matched length,
/// and the source span it read — never a score and never a selection.
struct query_return final {
  std::uint32_t state{};
  std::uint32_t matched{};
  std::uint32_t span_start{};
  std::uint32_t span_length{};
  std::uint32_t reached_by_first{};
};

/// The resident query kernel.
///
/// **Both arenas arrive by value and both laws take them by const reference.**
/// The ecology itself stays in resident storage; what enters the frame is two
/// span-and-counter values. A device path that founded, linked, or froze
/// anything would not compile against these signatures.
__global__ void resident_query_kernel(
    const suffix_arena suffix,
    const incidence_arena incidence,
    std::uint32_t path_length,
    std::uint32_t query_paths,
    query_return* returns) {
  const std::uint32_t slot =
      blockIdx.x * blockDim.x + threadIdx.x;
  if (slot >= query_paths) {
    return;
  }
  suffix_symbol path[16]{};
  const std::uint32_t held = path_length < 16U ? path_length : 16U;
  for (std::uint32_t step = 0; step < held; ++step) {
    path[step] = mount_germ(slot, step);
  }
  query_return answered{};
  answered.state = organ::suffix_law::follow_read(suffix, path, held, answered.matched);
  const source_span found = organ::incidence_law::span(incidence, answered.state);
  answered.span_start = found.start;
  answered.span_length = found.length;
  answered.reached_by_first =
      organ::incidence_law::reaches(incidence, answered.state, slot) ? 1U : 0U;
  returns[slot] = answered;
}

/// One managed reservation. The apparatus owns every page; the interior only
/// ever receives the span.
template<class Value>
[[nodiscard]] bool try_reserve(
    structure::resident_span<Value>& span,
    std::uint32_t extent,
    std::uint64_t& octets) noexcept {
  void* pages = nullptr;
  const std::size_t width = sizeof(Value) * static_cast<std::size_t>(extent);
  if (cudaMallocManaged(&pages, width) != cudaSuccess || pages == nullptr) {
    return false;
  }
  if (cudaMemset(pages, 0, width) != cudaSuccess) {
    return false;
  }
  span = structure::resident_span<Value>{static_cast<Value*>(pages), extent};
  octets = octets + static_cast<std::uint64_t>(width);
  return true;
}

void release(void* pages) noexcept {
  if (pages != nullptr) {
    static_cast<void>(cudaFree(pages));
  }
}

}  // namespace

resident_mount_receipt mount_resident_ecology(resident_mount_request request) noexcept {
  resident_mount_receipt receipt{};
  if (request.sources == 0 || request.path_length == 0 || request.path_length > 16 ||
      request.state_capacity < 2 || request.transition_capacity == 0 ||
      request.occurrence_capacity == 0 || request.query_paths == 0 ||
      request.query_paths > request.sources) {
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

  suffix_arena suffix{};
  incidence_arena incidence{};
  query_return* returns = nullptr;
  std::uint64_t octets = 0;
  const bool reserved =
      try_reserve(suffix.states, request.state_capacity, octets) &&
      try_reserve(suffix.transitions, request.transition_capacity, octets) &&
      try_reserve(suffix.next, request.transition_capacity, octets) &&
      try_reserve(incidence.staged, request.occurrence_capacity, octets) &&
      try_reserve(incidence.staged_next, request.occurrence_capacity, octets) &&
      try_reserve(incidence.ordered_sources, request.occurrence_capacity, octets) &&
      try_reserve(incidence.spans, request.state_capacity, octets) &&
      try_reserve(incidence.direct_head, request.state_capacity, octets) &&
      try_reserve(incidence.first_child, request.state_capacity, octets) &&
      try_reserve(incidence.next_sibling, request.state_capacity, octets) &&
      try_reserve(incidence.walk_stack, request.state_capacity, octets);
  if (!reserved ||
      cudaMallocManaged(reinterpret_cast<void**>(&returns),
          sizeof(query_return) * request.query_paths) != cudaSuccess) {
    receipt.state = executor_status::allocation_refused;
    return receipt;
  }
  receipt.resident_octets = octets;
  receipt.frame_octets = sizeof(suffix_arena) + sizeof(incidence_arena);

  if (!organ::suffix_law::try_found_root(suffix) ||
      !organ::incidence_law::try_open(incidence)) {
    receipt.state = executor_status::allocation_refused;
    return receipt;
  }
  // Formation is the host's, entirely. The card never runs it.
  for (std::uint32_t source = 0; source < request.sources; ++source) {
    organ::suffix_law::separate(suffix);
    for (std::uint32_t step = 0; step < request.path_length; ++step) {
      const std::uint32_t state =
          organ::suffix_law::extend(suffix, mount_germ(source, step));
      if (state == no_state || !organ::incidence_law::try_admit(incidence, state, source)) {
        receipt.state = executor_status::invalid_aperture;
        return receipt;
      }
    }
    if (organ::suffix_law::extend(suffix,
            suffix_symbol{organ::symbol_kind::boundary, source}) == no_state) {
      receipt.state = executor_status::invalid_aperture;
      return receipt;
    }
  }
  if (!organ::incidence_law::freeze(incidence, suffix)) {
    receipt.state = executor_status::invalid_aperture;
    return receipt;
  }
  receipt.states = suffix.states_used;
  receipt.transitions = suffix.transitions_used;
  receipt.occurrences = incidence.staged_used;
  receipt.ordered = incidence.ordered_used;
  receipt.formation_steps = incidence.formation_steps;
  receipt.lookup_steps = suffix.lookup_steps;

  const std::uint64_t formation_before = incidence.formation_steps;
  const std::uint32_t states_before = suffix.states_used;
  const std::uint32_t transitions_before = suffix.transitions_used;
  const std::uint32_t ordered_before = incidence.ordered_used;

  // A power-of-two block, so the grid is a shift. No integer division appears
  // anywhere in this translation unit: on sm_89 a 64-bit divide lowers through
  // a Newton iteration whose opening instruction converts to a non-integer carrier,
  // and no such carrier may be reachable from a kernel.
  const std::uint32_t block = 128;
  const std::uint32_t grid = (request.query_paths + (block - 1U)) >> 7U;
  resident_query_kernel<<<grid, block>>>(
      suffix, incidence, request.path_length, request.query_paths, returns);
  if (cudaGetLastError() != cudaSuccess) {
    receipt.state = executor_status::launch_refused;
    return receipt;
  }
  if (cudaDeviceSynchronize() != cudaSuccess) {
    receipt.state = executor_status::synchronization_refused;
    return receipt;
  }

  for (std::uint32_t slot = 0; slot < request.query_paths; ++slot) {
    suffix_symbol path[16]{};
    for (std::uint32_t step = 0; step < request.path_length; ++step) {
      path[step] = mount_germ(slot, step);
    }
    std::uint32_t matched = 0;
    const std::uint32_t state =
        organ::suffix_law::follow_read(suffix, path, request.path_length, matched);
    const source_span found = organ::incidence_law::span(incidence, state);
    const std::uint32_t reached =
        organ::incidence_law::reaches(incidence, state, slot) ? 1U : 0U;
    if (returns[slot].state != state || returns[slot].matched != matched ||
        returns[slot].span_start != found.start ||
        returns[slot].span_length != found.length ||
        returns[slot].reached_by_first != reached) {
      receipt.parity_failures = receipt.parity_failures + 1U;
    }
  }
  receipt.device_queries = request.query_paths;
  receipt.host_replay_work = incidence.formation_steps - formation_before;
  receipt.standing_unchanged = suffix.states_used == states_before &&
      suffix.transitions_used == transitions_before &&
      incidence.ordered_used == ordered_before;
  receipt.state = executor_status::returned;

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
  release(returns);
  return receipt;
}

}  // namespace holonics::apparatus
