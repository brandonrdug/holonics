#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/causal_current_resident.hpp>

namespace holonics::apparatus {
namespace {

struct current_device_storage final {
  current::current_mount_batch* mount{};
  current::resident_causal_body* bodies{};
  current::current_batch_observation* observation{};
};

void release(current_device_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.bodies != nullptr) { static_cast<void>(cudaFree(storage.bodies)); }
  if (storage.observation != nullptr) { static_cast<void>(cudaFree(storage.observation)); }
  storage = {};
}

[[nodiscard]] bool allocate(current_device_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(current::current_mount_batch)) == cudaSuccess &&
      cudaMalloc(&storage.bodies,
          sizeof(current::resident_causal_body) * current::current_case_capacity) == cudaSuccess &&
      cudaMalloc(&storage.observation, sizeof(current::current_batch_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval exact_interval(std::uint64_t value) noexcept {
  return calibrated_integer_interval{telemetry_status::calibrated_interval,
      exact::word{value}, exact::word{value}, exact::word{1}};
}

}  // namespace

causal_current_executor_receipt execute_causal_current(
    const current::current_mount_batch& mount,
    current::current_batch_observation& observation,
    std::uint32_t required_device_major,
    std::uint32_t required_device_minor) noexcept {
  causal_current_executor_receipt receipt{};
  if (mount.count == 0 || mount.count > current::current_case_capacity) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = causal_current_executor_status::device_unavailable;
    receipt.obstruction = current::current_obstruction::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = causal_current_executor_status::device_unavailable;
    receipt.obstruction = current::current_obstruction::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  if (receipt.device_major < required_device_major ||
      (receipt.device_major == required_device_major &&
       receipt.device_minor < required_device_minor)) {
    receipt.state = causal_current_executor_status::device_unavailable;
    receipt.obstruction = current::current_obstruction::device_unavailable;
    return receipt;
  }
  current_device_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = causal_current_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.bodies, 0,
          sizeof(current::resident_causal_body) * current::current_case_capacity) != cudaSuccess ||
      cudaMemset(storage.observation, 0, sizeof(current::current_batch_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = causal_current_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_current_mount(storage.mount, storage.bodies, storage.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = causal_current_executor_status::launch_refused;
    return receipt;
  }
  static_cast<void>(cudaFree(storage.mount));
  storage.mount = nullptr;
  if (launch_current_advance(storage.bodies, storage.observation) != cudaSuccess ||
      launch_current_observe(storage.bodies, storage.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.observation, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = causal_current_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  const std::uint64_t resident_bytes =
      sizeof(current::resident_causal_body) * mount.count + sizeof(observation);
  receipt.state = causal_current_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_body_bytes = exact::word{resident_bytes};
  receipt.launched_threads = exact::word{72};
  receipt.kernel_launches = exact::word{3};
  receipt.host_semantic_candidates = exact::word{0};
  receipt.host_oracle_replays = exact::word{0};
  receipt.logical.read_support = exact::word{mount.count};
  receipt.logical.change_support = exact::word{mount.count};
  receipt.logical.alternatives_retained = exact::word{1};
  receipt.logical.obstructions_retained = exact::word{1};
  receipt.logical.reservations_consumed = exact::word{mount.count};
  receipt.physical.resident_bytes = exact_interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
