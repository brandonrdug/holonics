#include <cuda_runtime.h>

#include <holonics/apparatus/return_conditioning_resident.hpp>

namespace holonics::apparatus {
namespace {

struct return_conditioning_storage final {
  return_conditioning_mount* mount{};
  event::resident_theorem_production* production{};
  event::resident_theorem_production* ablation{};
  event::theorem_production_rest_record* projected{};
  event::theorem_production_rest_record* handoff{};
  event::dependent_theorem_setup* setup{};
  event::return_conditioning_observation* resident{};
  event::return_conditioning_observation* returned{};
};

void release(return_conditioning_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.production != nullptr) { static_cast<void>(cudaFree(storage.production)); }
  if (storage.ablation != nullptr) { static_cast<void>(cudaFree(storage.ablation)); }
  if (storage.projected != nullptr) { static_cast<void>(cudaFree(storage.projected)); }
  if (storage.handoff != nullptr) { static_cast<void>(cudaFree(storage.handoff)); }
  if (storage.setup != nullptr) { static_cast<void>(cudaFree(storage.setup)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  storage = {};
}

[[nodiscard]] bool allocate(return_conditioning_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(return_conditioning_mount)) == cudaSuccess &&
      cudaMalloc(&storage.production, sizeof(event::resident_theorem_production)) == cudaSuccess &&
      cudaMalloc(&storage.ablation, sizeof(event::resident_theorem_production)) == cudaSuccess &&
      cudaMalloc(&storage.projected, sizeof(event::theorem_production_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.handoff, sizeof(event::theorem_production_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.setup, sizeof(event::dependent_theorem_setup)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(event::return_conditioning_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(event::return_conditioning_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value}, exact::word{value},
      exact::word{1}};
}

}  // namespace

return_conditioning_executor_receipt execute_return_conditioning(
    const return_conditioning_mount& mount,
    event::return_conditioning_observation& observation,
    event::theorem_production_rest_record& handoff,
    event::dependent_theorem_setup& setup) noexcept {
  return_conditioning_executor_receipt receipt{};
  if (!organ::valid_theorem_foundation(mount.foundation) ||
      mount.inherited.integrity != event::theorem_production_rest_integrity(mount.inherited) ||
      mount.question.identity.value() == 0 || mount.question.required_returned_fiber.value() == 0) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = return_conditioning_executor_status::device_unavailable; return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = return_conditioning_executor_status::device_unavailable; return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  return_conditioning_storage storage{};
  if (!allocate(storage)) {
    release(storage); receipt.state = return_conditioning_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.production, 0, sizeof(event::resident_theorem_production)) != cudaSuccess ||
      cudaMemset(storage.ablation, 0, sizeof(event::resident_theorem_production)) != cudaSuccess ||
      cudaMemset(storage.projected, 0, sizeof(event::theorem_production_rest_record)) != cudaSuccess ||
      cudaMemset(storage.handoff, 0, sizeof(event::theorem_production_rest_record)) != cudaSuccess ||
      cudaMemset(storage.setup, 0, sizeof(event::dependent_theorem_setup)) != cudaSuccess ||
      cudaMemset(storage.resident, 0, sizeof(event::return_conditioning_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0, sizeof(event::return_conditioning_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage); receipt.state = return_conditioning_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_return_conditioning_mount(storage.mount, storage.production, storage.resident) !=
          cudaSuccess ||
      launch_return_conditioning_ablation(storage.mount, storage.projected, storage.ablation,
          storage.setup, storage.resident) != cudaSuccess ||
      launch_return_conditioning_rest(storage.production, storage.handoff, storage.resident) !=
          cudaSuccess ||
      launch_return_conditioning_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation), cudaMemcpyDeviceToHost) !=
          cudaSuccess ||
      cudaMemcpy(&handoff, storage.handoff, sizeof(handoff), cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&setup, storage.setup, sizeof(setup), cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = return_conditioning_executor_status::launch_refused;
    return receipt;
  }
  release(storage);
  if (!observation.production_remount.same_body || !observation.production.available ||
      !observation.exclusion.exact || observation.ablated.available ||
      !observation.dependency_exact || !observation.handoff.returned) {
    receipt.state = return_conditioning_executor_status::conditioning_refused; return receipt;
  }
  const std::uint64_t resident_bytes = sizeof(return_conditioning_mount) +
      sizeof(event::resident_theorem_production) * 2U +
      sizeof(event::theorem_production_rest_record) * 2U +
      sizeof(event::dependent_theorem_setup) +
      sizeof(event::return_conditioning_observation) * 2U;
  receipt.state = return_conditioning_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)};
  receipt.bytes_from_device = exact::word{sizeof(observation) + sizeof(handoff) + sizeof(setup)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.kernel_launches = exact::word{4};
  receipt.launched_threads = exact::word{4};
  receipt.host_semantic_events = exact::word{0};
  receipt.engine_source_reads = exact::word{0};
  receipt.exterior_retrieval_calls = exact::word{0};
  receipt.developmental_source_bytes = exact::word{0};
  receipt.logical.read_support = exact::word{4};
  receipt.logical.change_support = exact::word{1};
  receipt.logical.alternatives_retained = exact::word{1};
  receipt.logical.obstructions_retained = exact::word{1};
  receipt.logical.reservations_consumed = exact::word{0};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
