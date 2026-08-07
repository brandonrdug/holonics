#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/reflective_codec_resident.hpp>

namespace holonics::apparatus {
namespace {

struct codec_storage final {
  reflective_codec_mount* mount{};
  reflective_codec_deed* deed{};
  event::resident_reflective_codec* body{};
  event::reflective_codec_rest_record* rest{};
  reflective_codec_observation* resident{};
  reflective_codec_observation* returned{};
};

void release(codec_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.deed != nullptr) { static_cast<void>(cudaFree(storage.deed)); }
  if (storage.body != nullptr) { static_cast<void>(cudaFree(storage.body)); }
  if (storage.rest != nullptr) { static_cast<void>(cudaFree(storage.rest)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  storage = {};
}

[[nodiscard]] bool allocate(codec_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(reflective_codec_mount)) == cudaSuccess &&
      cudaMalloc(&storage.deed, sizeof(reflective_codec_deed)) == cudaSuccess &&
      cudaMalloc(&storage.body, sizeof(event::resident_reflective_codec)) == cudaSuccess &&
      cudaMalloc(&storage.rest, sizeof(event::reflective_codec_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(reflective_codec_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(reflective_codec_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value},
      exact::word{value}, exact::word{1}};
}

}  // namespace

reflective_codec_executor_receipt execute_reflective_codec(
    const reflective_codec_mount& mount,
    reflective_codec_observation& observation) noexcept {
  reflective_codec_executor_receipt receipt{};
  if (!codec::valid_environment(mount.environment) || !mount.source_detached ||
      mount.original_material != mount.relocated_material ||
      mount.original_path == mount.relocated_path) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = reflective_codec_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = reflective_codec_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  codec_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = reflective_codec_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.body, 0, sizeof(event::resident_reflective_codec)) != cudaSuccess ||
      cudaMemset(storage.rest, 0, sizeof(event::reflective_codec_rest_record)) != cudaSuccess ||
      cudaMemset(storage.resident, 0, sizeof(reflective_codec_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0, sizeof(reflective_codec_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess ||
      cudaMemcpy(storage.deed, &mount.deed, sizeof(mount.deed),
          cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = reflective_codec_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_reflective_codec_mount(storage.mount, storage.body, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = reflective_codec_executor_status::launch_refused;
    return receipt;
  }
  static_cast<void>(cudaFree(storage.mount));
  storage.mount = nullptr;
  if (launch_reflective_codec_revise_rest(storage.deed, storage.body, storage.rest,
          storage.resident) != cudaSuccess || cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = reflective_codec_executor_status::synchronization_refused;
    return receipt;
  }
  static_cast<void>(cudaFree(storage.body));
  storage.body = nullptr;
  if (cudaMalloc(&storage.body, sizeof(event::resident_reflective_codec)) != cudaSuccess ||
      cudaMemset(storage.body, 0, sizeof(event::resident_reflective_codec)) != cudaSuccess ||
      launch_reflective_codec_remount(storage.deed, storage.rest, storage.body,
          storage.resident) != cudaSuccess ||
      launch_reflective_codec_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = reflective_codec_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  const std::uint64_t resident = sizeof(reflective_codec_deed) +
      sizeof(event::resident_reflective_codec) + sizeof(event::reflective_codec_rest_record) +
      sizeof(reflective_codec_observation) * 2U;
  receipt.state = reflective_codec_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount) + sizeof(mount.deed)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_bytes = exact::word{resident};
  receipt.launched_threads = exact::word{4};
  receipt.kernel_launches = exact::word{4};
  receipt.host_semantic_events = exact::word{0};
  receipt.logical.read_support = exact::word{2};
  receipt.logical.change_support = exact::word{1};
  receipt.logical.alternatives_retained = exact::word{2};
  receipt.logical.obstructions_retained = exact::word{4};
  receipt.logical.reservations_consumed = exact::word{1};
  receipt.physical.resident_bytes = interval(resident);
  return receipt;
}

}  // namespace holonics::apparatus
