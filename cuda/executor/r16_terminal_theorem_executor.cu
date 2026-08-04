#include <cuda_runtime.h>

#include <holonics/apparatus/returned_theorem_checker_process.hpp>
#include <holonics/apparatus/terminal_theorem_resident.hpp>

namespace holonics::apparatus {
namespace {

struct terminal_theorem_storage final {
  terminal_theorem_mount* mount{};
  event::theorem_production_rest_record* projected{};
  event::resident_dependent_theorem_production* production{};
  event::resident_dependent_theorem_production* ablation{};
  event::terminal_theorem_rest_record* rest{};
  event::terminal_theorem_rest_record* handoff{};
  event::terminal_theorem_observation* resident{};
  event::terminal_theorem_observation* returned{};
  event::checker_raw_return* raw{};
};

void release(terminal_theorem_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.projected != nullptr) { static_cast<void>(cudaFree(storage.projected)); }
  if (storage.production != nullptr) { static_cast<void>(cudaFree(storage.production)); }
  if (storage.ablation != nullptr) { static_cast<void>(cudaFree(storage.ablation)); }
  if (storage.rest != nullptr) { static_cast<void>(cudaFree(storage.rest)); }
  if (storage.handoff != nullptr) { static_cast<void>(cudaFree(storage.handoff)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  if (storage.raw != nullptr) { static_cast<void>(cudaFree(storage.raw)); }
  storage = {};
}

[[nodiscard]] bool allocate(terminal_theorem_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(terminal_theorem_mount)) == cudaSuccess &&
      cudaMalloc(&storage.projected, sizeof(event::theorem_production_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.production,
          sizeof(event::resident_dependent_theorem_production)) == cudaSuccess &&
      cudaMalloc(&storage.ablation,
          sizeof(event::resident_dependent_theorem_production)) == cudaSuccess &&
      cudaMalloc(&storage.rest, sizeof(event::terminal_theorem_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.handoff, sizeof(event::terminal_theorem_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(event::terminal_theorem_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(event::terminal_theorem_observation)) == cudaSuccess &&
      cudaMalloc(&storage.raw, sizeof(event::checker_raw_return)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value}, exact::word{value},
      exact::word{1}};
}

}  // namespace

terminal_theorem_executor_receipt execute_terminal_theorem(
    const terminal_theorem_mount& mount,
    const lean_process_configuration& process,
    event::terminal_theorem_observation& observation,
    event::terminal_theorem_rest_record& handoff) noexcept {
  terminal_theorem_executor_receipt receipt{};
  if (!organ::valid_theorem_foundation(mount.foundation) ||
      mount.inherited.integrity != event::theorem_production_rest_integrity(mount.inherited) ||
      mount.setup.integrity != event::dependent_setup_integrity(mount.setup)) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = terminal_theorem_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = terminal_theorem_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  terminal_theorem_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = terminal_theorem_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.projected, 0, sizeof(event::theorem_production_rest_record)) != cudaSuccess ||
      cudaMemset(storage.production, 0,
          sizeof(event::resident_dependent_theorem_production)) != cudaSuccess ||
      cudaMemset(storage.ablation, 0,
          sizeof(event::resident_dependent_theorem_production)) != cudaSuccess ||
      cudaMemset(storage.rest, 0, sizeof(event::terminal_theorem_rest_record)) != cudaSuccess ||
      cudaMemset(storage.handoff, 0, sizeof(event::terminal_theorem_rest_record)) != cudaSuccess ||
      cudaMemset(storage.resident, 0,
          sizeof(event::terminal_theorem_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0,
          sizeof(event::terminal_theorem_observation)) != cudaSuccess ||
      cudaMemset(storage.raw, 0, sizeof(event::checker_raw_return)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = terminal_theorem_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_terminal_theorem_stage(storage.mount, storage.projected, storage.production,
          storage.ablation, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.resident, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess ||
      observation.checker_stage != event::checker_stage_status::exact ||
      !observation.dependency_exact) {
    release(storage);
    receipt.state = terminal_theorem_executor_status::generation_refused;
    return receipt;
  }
  event::checker_raw_return raw{};
  receipt.process = run_returned_theorem_checker_process(
      observation.checker_face, observation.outbound, process, raw);
  if (!receipt.process.returned()) {
    release(storage);
    receipt.state = terminal_theorem_executor_status::process_refused;
    return receipt;
  }
  if (cudaMemcpy(storage.raw, &raw, sizeof(raw), cudaMemcpyHostToDevice) != cudaSuccess ||
      launch_terminal_theorem_resume(storage.raw, storage.production, storage.resident) !=
          cudaSuccess || cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = terminal_theorem_executor_status::return_refused;
    return receipt;
  }
  if (launch_terminal_theorem_rest(storage.production, storage.rest, storage.resident) !=
          cudaSuccess ||
      launch_terminal_theorem_remount(storage.mount, storage.rest, storage.handoff,
          storage.production, storage.resident) != cudaSuccess ||
      launch_terminal_theorem_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&handoff, storage.handoff, sizeof(handoff),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = terminal_theorem_executor_status::rest_refused;
    return receipt;
  }
  release(storage);
  if (observation.typed.state != event::checker_return_status::accepted ||
      !observation.rest.returned || !observation.remount.same_body ||
      !observation.remount.both_returns_preserved || !observation.handoff.returned ||
      !observation.handoff_continuation_valid) {
    receipt.state = terminal_theorem_executor_status::rest_refused;
    return receipt;
  }
  const std::uint64_t resident_bytes = sizeof(terminal_theorem_mount) +
      sizeof(event::theorem_production_rest_record) +
      sizeof(event::resident_dependent_theorem_production) * 2U +
      sizeof(event::terminal_theorem_rest_record) * 2U +
      sizeof(event::terminal_theorem_observation) * 2U + sizeof(event::checker_raw_return);
  receipt.state = terminal_theorem_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount) + sizeof(raw)};
  receipt.bytes_from_device = exact::word{sizeof(observation) * 2U + sizeof(handoff)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.kernel_launches = exact::word{5};
  receipt.launched_threads = exact::word{5};
  receipt.host_semantic_events = exact::word{0};
  receipt.engine_source_reads = exact::word{0};
  receipt.exterior_retrieval_calls = exact::word{0};
  receipt.developmental_source_bytes = exact::word{0};
  receipt.logical.read_support = exact::word{7};
  receipt.logical.change_support = exact::word{4};
  receipt.logical.alternatives_retained = exact::word{1};
  receipt.logical.obstructions_retained = exact::word{2};
  receipt.logical.reservations_consumed = exact::word{2};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
