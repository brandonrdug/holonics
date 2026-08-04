#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/lean_checker_resident.hpp>

namespace holonics::apparatus {
namespace {

struct checker_storage final {
  lean_checker_mount* mount{};
  event::resident_checker_current* current{};
  event::checker_observation* resident{};
  event::checker_observation* returned{};
  event::checker_raw_return* raw{};
};

void release(checker_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.current != nullptr) { static_cast<void>(cudaFree(storage.current)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  if (storage.raw != nullptr) { static_cast<void>(cudaFree(storage.raw)); }
  storage = {};
}

[[nodiscard]] bool allocate(checker_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(lean_checker_mount)) == cudaSuccess &&
      cudaMalloc(&storage.current, sizeof(event::resident_checker_current)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(event::checker_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(event::checker_observation)) == cudaSuccess &&
      cudaMalloc(&storage.raw, sizeof(event::checker_raw_return)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value}, exact::word{value},
      exact::word{1}};
}

}  // namespace

lean_checker_executor_receipt execute_lean_checker(const lean_checker_mount& mount,
    const lean_process_configuration& process,
    event::checker_observation& observation) noexcept {
  lean_checker_executor_receipt receipt{};
  if (mount.source.identity.value() == 0 || mount.source.passage.value() == 0 ||
      mount.source.byte_count == 0 || mount.body_seed == 0) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = lean_checker_executor_status::device_unavailable; return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = lean_checker_executor_status::device_unavailable; return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  checker_storage storage{};
  if (!allocate(storage)) {
    release(storage); receipt.state = lean_checker_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.current, 0, sizeof(event::resident_checker_current)) != cudaSuccess ||
      cudaMemset(storage.resident, 0, sizeof(event::checker_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0, sizeof(event::checker_observation)) != cudaSuccess ||
      cudaMemset(storage.raw, 0, sizeof(event::checker_raw_return)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage); receipt.state = lean_checker_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_lean_checker_stage(storage.mount, storage.current, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.resident, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = lean_checker_executor_status::stage_refused;
    return receipt;
  }
  if (observation.stage != event::checker_stage_status::exact ||
      !observation.pending_before_process) {
    release(storage); receipt.state = lean_checker_executor_status::stage_refused;
    return receipt;
  }
  event::checker_raw_return raw{};
  receipt.process = run_lean_checker_process(
      observation.checker_face, observation.outbound, process, raw);
  if (!receipt.process.returned()) {
    release(storage); receipt.state = lean_checker_executor_status::process_refused;
    return receipt;
  }
  if (cudaMemcpy(storage.raw, &raw, sizeof(raw), cudaMemcpyHostToDevice) != cudaSuccess ||
      launch_lean_checker_resume(storage.raw, storage.current, storage.resident) != cudaSuccess ||
      launch_lean_checker_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = lean_checker_executor_status::resume_refused;
    return receipt;
  }
  release(storage);
  if (!observation.morphology.returned_difference_applied ||
      observation.pending_after_return || !observation.passage_preserved) {
    receipt.state = lean_checker_executor_status::resume_refused; return receipt;
  }
  const std::uint64_t resident_bytes = sizeof(lean_checker_mount) +
      sizeof(event::resident_checker_current) + sizeof(event::checker_observation) * 2U +
      sizeof(event::checker_raw_return);
  receipt.state = lean_checker_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount) + sizeof(raw)};
  receipt.bytes_from_device = exact::word{sizeof(observation) * 2U};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.kernel_launches = exact::word{3};
  receipt.launched_threads = exact::word{3};
  receipt.host_semantic_events = exact::word{0};
  receipt.logical.read_support = exact::word{2};
  receipt.logical.change_support = exact::word{2};
  receipt.logical.alternatives_retained = exact::word{1};
  receipt.logical.obstructions_retained = exact::word{
      observation.typed.state == event::checker_return_status::accepted ? 0U : 1U};
  receipt.logical.reservations_consumed = exact::word{1};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
