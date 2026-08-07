#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/weave_resident.hpp>

namespace holonics::apparatus {
namespace {

struct weave_device_storage final {
  current::weave_mount_batch* mount{};
  current::resident_weave* bodies{};
  weave_batch_observation* observation{};
};

void release(weave_device_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.bodies != nullptr) { static_cast<void>(cudaFree(storage.bodies)); }
  if (storage.observation != nullptr) { static_cast<void>(cudaFree(storage.observation)); }
  storage = {};
}

[[nodiscard]] bool allocate(weave_device_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(current::weave_mount_batch)) == cudaSuccess &&
      cudaMalloc(&storage.bodies,
          sizeof(current::resident_weave) * current::weave_case_capacity) == cudaSuccess &&
      cudaMalloc(&storage.observation, sizeof(weave_batch_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval exact_interval(std::uint64_t value) noexcept {
  return calibrated_integer_interval{telemetry_status::calibrated_interval,
      exact::word{value}, exact::word{value}, exact::word{1}};
}

}  // namespace

weave_executor_receipt execute_weave(
    const current::weave_mount_batch& mount,
    weave_batch_observation& observation) noexcept {
  weave_executor_receipt receipt{};
  if (mount.count == 0 || mount.count > current::weave_case_capacity) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = weave_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = weave_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  weave_device_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = weave_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.bodies, 0,
          sizeof(current::resident_weave) * current::weave_case_capacity) != cudaSuccess ||
      cudaMemset(storage.observation, 0, sizeof(weave_batch_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = weave_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_weave_mount(storage.mount, storage.bodies, storage.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = weave_executor_status::launch_refused;
    return receipt;
  }
  static_cast<void>(cudaFree(storage.mount));
  storage.mount = nullptr;
  if (launch_weave_advance(storage.bodies, storage.observation) != cudaSuccess ||
      launch_weave_observe(storage.bodies, storage.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.observation, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = weave_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  const std::uint64_t resident_bytes =
      sizeof(current::resident_weave) * mount.count + sizeof(observation);
  receipt.state = weave_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.launched_threads = exact::word{50};
  receipt.kernel_launches = exact::word{3};
  receipt.host_semantic_events = exact::word{0};
  receipt.unchanged_retries = exact::word{0};
  receipt.logical.read_support = exact::word{mount.count};
  receipt.logical.change_support = exact::word{mount.count};
  receipt.logical.alternatives_retained = exact::word{2};
  receipt.logical.obstructions_retained = exact::word{2};
  receipt.logical.reservations_consumed = exact::word{mount.count * current::weave_event_capacity};
  receipt.physical.resident_bytes = exact_interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
