#include <cuda_runtime.h>

#include <holonics/apparatus/theorem_production_resident.hpp>

namespace holonics::apparatus {
namespace {

struct theorem_production_storage final {
  theorem_production_mount* mount{};
  event::resident_theorem_production* production{};
  event::theorem_production_rest_record* rest{};
  event::theorem_production_rest_record* handoff{};
  event::theorem_production_observation* resident{};
  event::theorem_production_observation* returned{};
  event::checker_raw_return* raw{};
};

void release(theorem_production_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.production != nullptr) { static_cast<void>(cudaFree(storage.production)); }
  if (storage.rest != nullptr) { static_cast<void>(cudaFree(storage.rest)); }
  if (storage.handoff != nullptr) { static_cast<void>(cudaFree(storage.handoff)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  if (storage.raw != nullptr) { static_cast<void>(cudaFree(storage.raw)); }
  storage = {};
}

[[nodiscard]] bool allocate(theorem_production_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(theorem_production_mount)) == cudaSuccess &&
      cudaMalloc(&storage.production, sizeof(event::resident_theorem_production)) == cudaSuccess &&
      cudaMalloc(&storage.rest, sizeof(event::theorem_production_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.handoff, sizeof(event::theorem_production_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(event::theorem_production_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(event::theorem_production_observation)) == cudaSuccess &&
      cudaMalloc(&storage.raw, sizeof(event::checker_raw_return)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value}, exact::word{value},
      exact::word{1}};
}

}  // namespace

theorem_production_executor_receipt execute_theorem_production(
    const theorem_production_mount& mount, const lean_process_configuration& process,
    event::theorem_production_observation& observation,
    event::theorem_production_rest_record& handoff) noexcept {
  theorem_production_executor_receipt receipt{};
  if (!organ::valid_theorem_foundation(mount.foundation) || mount.body_seed == 0 ||
      mount.question.identity.value() == 0 || mount.held_probe.identity.value() == 0) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = theorem_production_executor_status::device_unavailable; return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = theorem_production_executor_status::device_unavailable; return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  theorem_production_storage storage{};
  if (!allocate(storage)) {
    release(storage); receipt.state = theorem_production_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.production, 0, sizeof(event::resident_theorem_production)) != cudaSuccess ||
      cudaMemset(storage.rest, 0, sizeof(event::theorem_production_rest_record)) != cudaSuccess ||
      cudaMemset(storage.handoff, 0, sizeof(event::theorem_production_rest_record)) != cudaSuccess ||
      cudaMemset(storage.resident, 0, sizeof(event::theorem_production_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0, sizeof(event::theorem_production_observation)) != cudaSuccess ||
      cudaMemset(storage.raw, 0, sizeof(event::checker_raw_return)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage); receipt.state = theorem_production_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_theorem_production_stage(storage.mount, storage.production, storage.resident) !=
          cudaSuccess || cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.resident, sizeof(observation), cudaMemcpyDeviceToHost) !=
          cudaSuccess || observation.checker_stage != event::checker_stage_status::exact) {
    release(storage); receipt.state = theorem_production_executor_status::generation_refused;
    return receipt;
  }
  event::checker_raw_return raw{};
  receipt.process = run_lean_checker_process(observation.checker_face,
      observation.outbound, process, raw);
  if (!receipt.process.returned()) {
    release(storage); receipt.state = theorem_production_executor_status::process_refused;
    return receipt;
  }
  if (cudaMemcpy(storage.raw, &raw, sizeof(raw), cudaMemcpyHostToDevice) != cudaSuccess ||
      launch_theorem_production_resume(storage.raw, storage.production, storage.resident) !=
          cudaSuccess || cudaDeviceSynchronize() != cudaSuccess) {
    release(storage); receipt.state = theorem_production_executor_status::return_refused;
    return receipt;
  }
  if (launch_theorem_production_rest(storage.production, storage.rest, storage.resident) !=
          cudaSuccess ||
      launch_theorem_production_remount_probe(storage.mount, storage.rest, storage.handoff,
          storage.production, storage.resident) != cudaSuccess ||
      launch_theorem_production_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation), cudaMemcpyDeviceToHost) !=
          cudaSuccess ||
      cudaMemcpy(&handoff, storage.handoff, sizeof(handoff), cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = theorem_production_executor_status::rest_refused;
    return receipt;
  }
  release(storage);
  if (observation.typed.state != event::checker_return_status::accepted ||
      !observation.rest.returned || !observation.remount.same_body ||
      !observation.handoff.returned || !observation.behavior_changed ||
      !observation.ablation.consequence_lost) {
    receipt.state = theorem_production_executor_status::rest_refused; return receipt;
  }
  const std::uint64_t resident_bytes = sizeof(theorem_production_mount) +
      sizeof(event::resident_theorem_production) +
      sizeof(event::theorem_production_rest_record) * 2U +
      sizeof(event::theorem_production_observation) * 2U + sizeof(event::checker_raw_return);
  receipt.state = theorem_production_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount) + sizeof(raw)};
  receipt.bytes_from_device = exact::word{sizeof(observation) * 2U + sizeof(handoff)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.kernel_launches = exact::word{5};
  receipt.launched_threads = exact::word{5};
  receipt.host_semantic_events = exact::word{0};
  receipt.engine_source_reads = exact::word{0};
  receipt.logical.read_support = exact::word{5};
  receipt.logical.change_support = exact::word{4};
  receipt.logical.alternatives_retained = exact::word{1};
  receipt.logical.obstructions_retained = exact::word{2};
  receipt.logical.reservations_consumed = exact::word{2};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
