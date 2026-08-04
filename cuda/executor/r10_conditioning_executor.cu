#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/conditioning_resident.hpp>

namespace holonics::apparatus {
namespace {

struct conditioning_storage final {
  conditioning_foundation* foundation{};
  conditioning_passage* passage{};
  receiver::conditioning_question* held_out{};
  event::resident_conditioned_organ* production{};
  event::resident_conditioned_organ* ablation{};
  event::conditioned_organ_rest_record* rest{};
  conditioning_observation* resident{};
  conditioning_observation* returned{};
};

void release(conditioning_storage& storage) noexcept {
  if (storage.foundation != nullptr) { static_cast<void>(cudaFree(storage.foundation)); }
  if (storage.passage != nullptr) { static_cast<void>(cudaFree(storage.passage)); }
  if (storage.held_out != nullptr) { static_cast<void>(cudaFree(storage.held_out)); }
  if (storage.production != nullptr) { static_cast<void>(cudaFree(storage.production)); }
  if (storage.ablation != nullptr) { static_cast<void>(cudaFree(storage.ablation)); }
  if (storage.rest != nullptr) { static_cast<void>(cudaFree(storage.rest)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  storage = {};
}

[[nodiscard]] bool allocate(conditioning_storage& storage) noexcept {
  return cudaMalloc(&storage.foundation, sizeof(conditioning_foundation)) == cudaSuccess &&
      cudaMalloc(&storage.passage, sizeof(conditioning_passage)) == cudaSuccess &&
      cudaMalloc(&storage.held_out, sizeof(receiver::conditioning_question)) == cudaSuccess &&
      cudaMalloc(&storage.production, sizeof(event::resident_conditioned_organ)) == cudaSuccess &&
      cudaMalloc(&storage.ablation, sizeof(event::resident_conditioned_organ)) == cudaSuccess &&
      cudaMalloc(&storage.rest, sizeof(event::conditioned_organ_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(conditioning_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(conditioning_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value},
      exact::word{value}, exact::word{1}};
}

}  // namespace

conditioning_executor_receipt execute_conditioning(
    const conditioning_mount& mount,
    conditioning_observation& observation) noexcept {
  conditioning_executor_receipt receipt{};
  if (!organ::valid_morphology(mount.foundation.morphology) ||
      mount.foundation.production_seed == 0 || mount.foundation.ablation_seed == 0 ||
      mount.foundation.production_seed == mount.foundation.ablation_seed ||
      mount.held_out.identity.value() == 0 || mount.held_out.receiver.value() == 0) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = conditioning_executor_status::device_unavailable; return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = conditioning_executor_status::device_unavailable; return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  conditioning_storage storage{};
  if (!allocate(storage)) {
    release(storage); receipt.state = conditioning_executor_status::allocation_refused; return receipt;
  }
  if (cudaMemset(storage.production, 0, sizeof(event::resident_conditioned_organ)) != cudaSuccess ||
      cudaMemset(storage.ablation, 0, sizeof(event::resident_conditioned_organ)) != cudaSuccess ||
      cudaMemset(storage.rest, 0, sizeof(event::conditioned_organ_rest_record)) != cudaSuccess ||
      cudaMemset(storage.resident, 0, sizeof(conditioning_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0, sizeof(conditioning_observation)) != cudaSuccess ||
      cudaMemcpy(storage.foundation, &mount.foundation, sizeof(mount.foundation),
          cudaMemcpyHostToDevice) != cudaSuccess ||
      cudaMemcpy(storage.passage, &mount.passage, sizeof(mount.passage),
          cudaMemcpyHostToDevice) != cudaSuccess ||
      cudaMemcpy(storage.held_out, &mount.held_out, sizeof(mount.held_out),
          cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage); receipt.state = conditioning_executor_status::transfer_refused; return receipt;
  }
  if (launch_conditioning_mount(storage.foundation, storage.production, storage.resident) != cudaSuccess ||
      launch_conditioning_train(storage.passage, storage.held_out, storage.production,
          storage.resident) != cudaSuccess || cudaDeviceSynchronize() != cudaSuccess) {
    release(storage); receipt.state = conditioning_executor_status::launch_refused; return receipt;
  }
  static_cast<void>(cudaFree(storage.passage));
  storage.passage = nullptr;
  if (launch_conditioning_rest(storage.production, storage.rest, storage.resident) != cudaSuccess ||
      launch_conditioning_remount(storage.rest, storage.held_out, storage.production,
          storage.resident) != cudaSuccess ||
      launch_conditioning_ablation(storage.foundation, storage.held_out, storage.ablation,
          storage.resident) != cudaSuccess ||
      launch_conditioning_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = conditioning_executor_status::synchronization_refused; return receipt;
  }
  release(storage);
  const std::uint64_t resident = sizeof(conditioning_foundation) +
      sizeof(receiver::conditioning_question) + sizeof(event::resident_conditioned_organ) * 2U +
      sizeof(event::conditioned_organ_rest_record) + sizeof(conditioning_observation) * 2U;
  receipt.state = conditioning_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount.foundation) +
      sizeof(mount.passage) + sizeof(mount.held_out)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_bytes = exact::word{resident};
  receipt.passage_bytes_after_training = exact::word{0};
  receipt.launched_threads = exact::word{6};
  receipt.kernel_launches = exact::word{6};
  receipt.host_semantic_events = exact::word{0};
  receipt.logical.read_support = exact::word{3};
  receipt.logical.change_support = exact::word{5};
  receipt.logical.alternatives_retained = exact::word{2};
  receipt.logical.obstructions_retained = exact::word{5};
  receipt.logical.reservations_consumed = exact::word{1};
  receipt.physical.resident_bytes = interval(resident);
  return receipt;
}

}  // namespace holonics::apparatus
