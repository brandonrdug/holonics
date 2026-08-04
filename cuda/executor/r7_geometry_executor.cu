#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/receiver_geometry_resident.hpp>

namespace holonics::apparatus {
namespace {

struct geometry_device_storage final {
  receiver_geometry_mount* mount{};
  current::resident_weave* current{};
  receiver::resident_geometry* receiver{};
  receiver_geometry_observation* observation{};
};

void release(geometry_device_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.current != nullptr) { static_cast<void>(cudaFree(storage.current)); }
  if (storage.receiver != nullptr) { static_cast<void>(cudaFree(storage.receiver)); }
  if (storage.observation != nullptr) { static_cast<void>(cudaFree(storage.observation)); }
  storage = {};
}

[[nodiscard]] bool allocate(geometry_device_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(receiver_geometry_mount)) == cudaSuccess &&
      cudaMalloc(&storage.current, sizeof(current::resident_weave)) == cudaSuccess &&
      cudaMalloc(&storage.receiver, sizeof(receiver::resident_geometry)) == cudaSuccess &&
      cudaMalloc(&storage.observation, sizeof(receiver_geometry_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value},
      exact::word{value}, exact::word{1}};
}

}  // namespace

receiver_geometry_executor_receipt execute_receiver_geometry(
    const receiver_geometry_mount& mount,
    receiver_geometry_observation& observation) noexcept {
  receiver_geometry_executor_receipt receipt{};
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = receiver_geometry_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = receiver_geometry_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  geometry_device_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = receiver_geometry_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.current, 0, sizeof(current::resident_weave)) != cudaSuccess ||
      cudaMemset(storage.receiver, 0, sizeof(receiver::resident_geometry)) != cudaSuccess ||
      cudaMemset(storage.observation, 0, sizeof(receiver_geometry_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = receiver_geometry_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_receiver_geometry_mount(storage.mount, storage.current, storage.receiver) !=
          cudaSuccess || cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = receiver_geometry_executor_status::launch_refused;
    return receipt;
  }
  static_cast<void>(cudaFree(storage.mount));
  storage.mount = nullptr;
  if (launch_receiver_geometry_advance(storage.current, storage.receiver) != cudaSuccess ||
      launch_receiver_geometry_observe(storage.current, storage.receiver,
          storage.observation) != cudaSuccess || cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.observation, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = receiver_geometry_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  const std::uint64_t resident = sizeof(current::resident_weave) +
      sizeof(receiver::resident_geometry) + sizeof(receiver_geometry_observation);
  receipt.state = receiver_geometry_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_bytes = exact::word{resident};
  receipt.launched_threads = exact::word{14};
  receipt.kernel_launches = exact::word{3};
  receipt.host_semantic_deeds = exact::word{0};
  receipt.logical.read_support = exact::word{7};
  receipt.logical.change_support = exact::word{7};
  receipt.logical.alternatives_retained = exact::word{9};
  receipt.logical.obstructions_retained = exact::word{4};
  receipt.logical.reservations_consumed = exact::word{10};
  receipt.physical.resident_bytes = interval(resident);
  return receipt;
}

}  // namespace holonics::apparatus
