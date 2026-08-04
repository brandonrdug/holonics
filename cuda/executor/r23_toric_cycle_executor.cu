#include <cuda_runtime.h>

#include <holonics/apparatus/toric_cycle_resident.hpp>

namespace holonics::apparatus {
namespace {

struct toric_storage final {
  toric_cycle_mount* mount{};
  event::resident_toric_cycle* production{};
  event::toric_cycle_rest_record* rest{};
  event::toric_cycle_rest_record* handoff{};
  event::toric_cycle_observation* resident{};
  event::toric_cycle_observation* returned{};
  event::checker_raw_return* raw{};
};

void release(toric_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.production != nullptr) { static_cast<void>(cudaFree(storage.production)); }
  if (storage.rest != nullptr) { static_cast<void>(cudaFree(storage.rest)); }
  if (storage.handoff != nullptr) { static_cast<void>(cudaFree(storage.handoff)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  if (storage.raw != nullptr) { static_cast<void>(cudaFree(storage.raw)); }
  storage = {};
}

[[nodiscard]] bool allocate(toric_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(toric_cycle_mount)) == cudaSuccess &&
      cudaMalloc(&storage.production, sizeof(event::resident_toric_cycle)) == cudaSuccess &&
      cudaMalloc(&storage.rest, sizeof(event::toric_cycle_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.handoff, sizeof(event::toric_cycle_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(event::toric_cycle_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(event::toric_cycle_observation)) == cudaSuccess &&
      cudaMalloc(&storage.raw, sizeof(event::checker_raw_return)) == cudaSuccess;
}

[[nodiscard]] bool initialize(const toric_cycle_mount& mount,
    toric_storage& storage) noexcept {
  return cudaMemset(storage.production, 0, sizeof(event::resident_toric_cycle)) == cudaSuccess &&
      cudaMemset(storage.rest, 0, sizeof(event::toric_cycle_rest_record)) == cudaSuccess &&
      cudaMemset(storage.handoff, 0, sizeof(event::toric_cycle_rest_record)) == cudaSuccess &&
      cudaMemset(storage.resident, 0, sizeof(event::toric_cycle_observation)) == cudaSuccess &&
      cudaMemset(storage.returned, 0, sizeof(event::toric_cycle_observation)) == cudaSuccess &&
      cudaMemset(storage.raw, 0, sizeof(event::checker_raw_return)) == cudaSuccess &&
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value}, exact::word{value},
      exact::word{1}};
}

}  // namespace

toric_executor_receipt execute_toric_cycle(const toric_cycle_mount& mount,
    const lean_process_configuration& process, event::toric_cycle_observation& observation,
    event::toric_cycle_rest_record& handoff) noexcept {
  toric_executor_receipt receipt{};
  if (!organ::toric_fan_detail::valid_foundation(mount.foundation) ||
      mount.question.identity.value() == 0 || mount.question.receiver.value() == 0 ||
      mount.question.material.value() == 0 ||
      mount.inherited.integrity != event::cm_incidence_rest_integrity(mount.inherited)) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = toric_executor_status::device_unavailable; return receipt;
  }
  int major = 0; int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = toric_executor_status::device_unavailable; return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  toric_storage storage{};
  if (!allocate(storage)) { release(storage);
    receipt.state = toric_executor_status::allocation_refused; return receipt; }
  if (!initialize(mount, storage)) { release(storage);
    receipt.state = toric_executor_status::transfer_refused; return receipt; }
  if (launch_toric_mount(storage.mount, storage.production, storage.resident) != cudaSuccess ||
      launch_toric_derive(storage.mount, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(storage); receipt.state = toric_executor_status::derivation_refused; return receipt;
  }
  if (launch_toric_form(storage.mount, storage.production, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.resident, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess || !observation.inquiry.theory_formed ||
      observation.passage.checker_stage != event::checker_stage_status::exact) {
    release(storage); receipt.state = toric_executor_status::formation_refused; return receipt;
  }
  event::checker_raw_return raw{};
  const lean_source_view source{observation.passage.formal.passage,
      observation.passage.formal.identity, observation.passage.formal.bytes,
      observation.passage.formal.byte_count};
  receipt.process = run_lean_checker_source(source, observation.passage.outbound, process, raw);
  if (!receipt.process.returned()) { release(storage);
    receipt.state = toric_executor_status::process_refused; return receipt; }
  if (cudaMemcpy(storage.raw, &raw, sizeof(raw), cudaMemcpyHostToDevice) != cudaSuccess ||
      launch_toric_resume(storage.raw, storage.production, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      launch_toric_rest_remount(storage.production, storage.rest, storage.handoff,
          storage.resident) != cudaSuccess ||
      launch_toric_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&handoff, storage.handoff, sizeof(handoff),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = toric_executor_status::return_refused; return receipt;
  }
  release(storage);
  if (observation.passage.typed.state != event::checker_return_status::accepted ||
      !observation.rest.returned || !observation.remount.same_body ||
      !observation.remount.theory_preserved || !observation.handoff.returned ||
      !observation.final_can_continue) {
    receipt.state = toric_executor_status::rest_refused; return receipt;
  }
  const std::uint64_t resident_bytes = sizeof(toric_cycle_mount) +
      sizeof(event::resident_toric_cycle) + sizeof(event::toric_cycle_rest_record) * 2U +
      sizeof(event::toric_cycle_observation) * 2U + sizeof(event::checker_raw_return);
  receipt.state = toric_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount) + sizeof(raw)};
  receipt.bytes_from_device = exact::word{sizeof(observation) * 2U + sizeof(handoff)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.kernel_launches = exact::word{6}; receipt.launched_threads = exact::word{6};
  receipt.semantic_threads = exact::word{1}; receipt.host_semantic_events = exact::word{0};
  receipt.logical = {exact::word{72}, exact::word{9}, exact::word{12},
      exact::word{6}, exact::word{3}};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
