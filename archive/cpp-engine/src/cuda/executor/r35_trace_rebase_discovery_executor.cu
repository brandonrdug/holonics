#include <cuda_runtime_api.h>

#include <holonics/apparatus/trace_rebase_current_set.hpp>
#include <holonics/apparatus/trace_rebase_executor.hpp>
#include <holonics/apparatus/returned_theorem_checker_process.hpp>

namespace holonics::apparatus {
namespace {
struct storage final {
  trace_rebase_discovery_mount *mount{};
  unsigned char *resident{};
  event::trace_rebase_discovery_observation *observation{};
  event::trace_rebase_discovery_observation *returned{};
  organ::trace_rebase_workspace *workspace{};
  event::checker_raw_return *raw{};
  event::trace_rebase_rest_record *rest{};
  event::trace_rebase_rest_record *handoff{};
};
void release(storage &s) noexcept {
  static_cast<void>(cudaFree(s.mount));
  static_cast<void>(cudaFree(s.resident));
  static_cast<void>(cudaFree(s.observation));
  static_cast<void>(cudaFree(s.returned));
  static_cast<void>(cudaFree(s.workspace));
  static_cast<void>(cudaFree(s.raw));
  static_cast<void>(cudaFree(s.rest));
  static_cast<void>(cudaFree(s.handoff));
  s = {};
}
[[nodiscard]] bool allocate(storage &s) noexcept {
  return cudaMalloc(&s.mount, sizeof(*s.mount)) == cudaSuccess &&
         cudaMalloc(&s.resident, sizeof(event::resident_trace_rebase)) ==
             cudaSuccess &&
         cudaMalloc(&s.observation, sizeof(*s.observation)) == cudaSuccess &&
         cudaMalloc(&s.returned, sizeof(*s.returned)) == cudaSuccess &&
         cudaMalloc(&s.workspace, sizeof(*s.workspace)) == cudaSuccess &&
         cudaMalloc(&s.raw, sizeof(*s.raw)) == cudaSuccess &&
         cudaMalloc(&s.rest, sizeof(*s.rest)) == cudaSuccess &&
         cudaMalloc(&s.handoff, sizeof(*s.handoff)) == cudaSuccess;
}
[[nodiscard]] bool initialize(const trace_rebase_discovery_mount &mount,
                              storage &s) noexcept {
  return cudaMemcpy(s.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) ==
             cudaSuccess &&
         cudaMemset(s.observation, 0, sizeof(*s.observation)) == cudaSuccess &&
         cudaMemset(s.returned, 0, sizeof(*s.returned)) == cudaSuccess &&
         cudaMemset(s.workspace, 0, sizeof(*s.workspace)) == cudaSuccess &&
         cudaMemset(s.raw, 0, sizeof(*s.raw)) == cudaSuccess &&
         cudaMemset(s.rest, 0, sizeof(*s.rest)) == cudaSuccess &&
         cudaMemset(s.handoff, 0, sizeof(*s.handoff)) == cudaSuccess;
}
[[nodiscard]] bool select_device(trace_rebase_executor_receipt &r) noexcept {
  int count = 0, major = 0, minor = 0;
  if (cudaGetDeviceCount(&count) != cudaSuccess || count <= 0 ||
      cudaSetDevice(0) != cudaSuccess ||
      cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) !=
          cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) !=
          cudaSuccess)
    return false;
  r.device_major = static_cast<std::uint32_t>(major);
  r.device_minor = static_cast<std::uint32_t>(minor);
  return true;
}
} // namespace

trace_rebase_executor_receipt execute_trace_rebase_discovery(
    const trace_rebase_discovery_mount &mount,
    const lean_process_configuration &process,
    event::trace_rebase_discovery_observation &observation,
    organ::trace_rebase_workspace &workspace,
    event::trace_rebase_rest_record &handoff) noexcept {
  trace_rebase_executor_receipt receipt{};
  if (mount.inherited.integrity !=
      event::trace_fiber_rest_integrity(mount.inherited))
    return receipt;
  if (!select_device(receipt)) {
    receipt.state = trace_rebase_executor_status::device_unavailable;
    return receipt;
  }
  storage s{};
  if (!allocate(s)) {
    release(s);
    receipt.state = trace_rebase_executor_status::allocation_refused;
    return receipt;
  }
  if (!initialize(mount, s) ||
      launch_trace_rebase_mount(s.mount, s.resident, s.observation) !=
          cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(s);
    receipt.state = trace_rebase_executor_status::transfer_refused;
    return receipt;
  }
  trace_rebase_current_set currents{};
  bool exact = open_trace_rebase_currents(currents);
  for (std::uint8_t source = 0; exact && source < 3; ++source) {
    exact = launch_trace_rebase_states(s.mount, s.observation, source,
                                       currents.currents[source]) ==
            cudaSuccess;
    exact = exact &&
            launch_trace_rebase_edges(s.observation, source,
                                      currents.currents[source]) == cudaSuccess;
  }
  exact = exact && join_trace_rebase_currents(currents);
  close_trace_rebase_currents(currents);
  if (!exact ||
      launch_trace_rebase_close(
          reinterpret_cast<event::resident_trace_rebase *>(s.resident),
          s.observation, s.workspace) != cudaSuccess ||
      launch_trace_rebase_form_surface(
          reinterpret_cast<event::resident_trace_rebase *>(s.resident),
          s.observation) != cudaSuccess ||
      launch_trace_rebase_form(
          reinterpret_cast<event::resident_trace_rebase *>(s.resident),
          s.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, s.observation, sizeof(observation),
                 cudaMemcpyDeviceToHost) != cudaSuccess ||
      !observation.inquiry.theory_formed) {
    release(s);
    receipt.state = trace_rebase_executor_status::formation_refused;
    return receipt;
  }
  event::checker_raw_return raw{};
  const lean_source_view source{
      observation.passage.formal.passage, observation.passage.formal.identity,
      observation.passage.formal.bytes, observation.passage.formal.byte_count};
  receipt.checker = run_returned_theorem_checker_source(
      source, observation.passage.outbound, process, raw);
  if (!receipt.checker.returned()) {
    release(s);
    receipt.state = trace_rebase_executor_status::checker_process_refused;
    return receipt;
  }
  if (cudaMemcpy(s.raw, &raw, sizeof(raw), cudaMemcpyHostToDevice) !=
          cudaSuccess ||
      launch_trace_rebase_resume(
          s.raw, reinterpret_cast<event::resident_trace_rebase *>(s.resident),
          s.observation) != cudaSuccess ||
      launch_trace_rebase_rest(
          reinterpret_cast<event::resident_trace_rebase *>(s.resident), s.rest,
          s.handoff, s.observation) != cudaSuccess ||
      launch_trace_rebase_observe(s.observation, s.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, s.returned, sizeof(observation),
                 cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&workspace, s.workspace, sizeof(workspace),
                 cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&handoff, s.handoff, sizeof(handoff),
                 cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(s);
    receipt.state = trace_rebase_executor_status::checker_return_refused;
    return receipt;
  }
  const std::uint64_t bytes =
      sizeof(mount) + sizeof(event::resident_trace_rebase) +
      2U * sizeof(observation) + sizeof(workspace) + sizeof(raw) +
      2U * sizeof(handoff);
  release(s);
  if (observation.passage.typed.state !=
          event::checker_return_status::accepted ||
      !observation.rest.returned || !observation.remount.maps_preserved ||
      !observation.remount.differential_preserved ||
      !observation.handoff.returned) {
    receipt.state = trace_rebase_executor_status::rest_refused;
    return receipt;
  }
  receipt.state = trace_rebase_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount) + sizeof(raw)};
  receipt.bytes_from_device =
      exact::word{sizeof(observation) + sizeof(workspace) + sizeof(handoff)};
  receipt.resident_bytes = exact::word{bytes};
  receipt.kernel_launches = exact::word{13};
  receipt.launched_threads = exact::word{8'454};
  receipt.semantic_threads = exact::word{7'638};
  receipt.source_currents = exact::word{3};
  receipt.dependency_barriers = exact::word{1};
  receipt.physical.resident_bytes = {telemetry_status::calibrated_interval,
                                     exact::word{bytes}, exact::word{bytes},
                                     exact::word{1}};
  return receipt;
}

} // namespace holonics::apparatus
