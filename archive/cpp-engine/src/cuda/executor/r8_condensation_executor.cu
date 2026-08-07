#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/boundary_condensation_resident.hpp>

namespace holonics::apparatus {
namespace {

struct condensation_storage final {
  boundary_condensation_mount* mount{};
  event::resident_condensation* body{};
  boundary_condensation_observation* observation{};
};

void release(condensation_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.body != nullptr) { static_cast<void>(cudaFree(storage.body)); }
  if (storage.observation != nullptr) { static_cast<void>(cudaFree(storage.observation)); }
  storage = {};
}

[[nodiscard]] bool allocate(condensation_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(boundary_condensation_mount)) == cudaSuccess &&
      cudaMalloc(&storage.body, sizeof(event::resident_condensation)) == cudaSuccess &&
      cudaMalloc(&storage.observation, sizeof(boundary_condensation_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value},
      exact::word{value}, exact::word{1}};
}

}  // namespace

boundary_condensation_executor_receipt execute_boundary_condensation(
    const boundary_condensation_mount& mount,
    boundary_condensation_observation& observation) noexcept {
  boundary_condensation_executor_receipt receipt{};
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = boundary_condensation_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = boundary_condensation_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  condensation_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = boundary_condensation_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.body, 0, sizeof(event::resident_condensation)) != cudaSuccess ||
      cudaMemset(storage.observation, 0, sizeof(boundary_condensation_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = boundary_condensation_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_boundary_condensation_mount(storage.mount, storage.body) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = boundary_condensation_executor_status::launch_refused;
    return receipt;
  }
  static_cast<void>(cudaFree(storage.mount));
  storage.mount = nullptr;
  if (launch_boundary_condensation_advance(storage.body) != cudaSuccess ||
      launch_boundary_condensation_observe(storage.body, storage.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.observation, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = boundary_condensation_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  const std::uint64_t resident =
      sizeof(event::resident_condensation) + sizeof(boundary_condensation_observation);
  receipt.state = boundary_condensation_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_bytes = exact::word{resident};
  receipt.launched_threads = exact::word{3};
  receipt.kernel_launches = exact::word{3};
  receipt.host_semantic_events = exact::word{0};
  receipt.logical.read_support = exact::word{8};
  receipt.logical.change_support = exact::word{4};
  receipt.logical.alternatives_retained = exact::word{2};
  receipt.logical.obstructions_retained = exact::word{4};
  receipt.logical.reservations_consumed = exact::word{5};
  receipt.physical.resident_bytes = interval(resident);
  return receipt;
}

}  // namespace holonics::apparatus
