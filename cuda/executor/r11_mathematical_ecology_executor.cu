#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/mathematical_ecology_resident.hpp>

namespace holonics::apparatus {
namespace {

struct mathematical_ecology_storage final {
  mathematical_ecology_mount* mount{};
  event::resident_mathematical_ecology* canonical{};
  event::resident_mathematical_ecology* reordered{};
  mathematical_ecology_observation* resident{};
  mathematical_ecology_observation* returned{};
};

void release(mathematical_ecology_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.canonical != nullptr) { static_cast<void>(cudaFree(storage.canonical)); }
  if (storage.reordered != nullptr) { static_cast<void>(cudaFree(storage.reordered)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  storage = {};
}

[[nodiscard]] bool allocate(mathematical_ecology_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(mathematical_ecology_mount)) == cudaSuccess &&
      cudaMalloc(&storage.canonical, sizeof(event::resident_mathematical_ecology)) == cudaSuccess &&
      cudaMalloc(&storage.reordered, sizeof(event::resident_mathematical_ecology)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(mathematical_ecology_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(mathematical_ecology_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value},
      exact::word{value}, exact::word{1}};
}

}  // namespace

mathematical_ecology_executor_receipt execute_mathematical_ecology(
    const mathematical_ecology_mount& mount,
    mathematical_ecology_observation& observation) noexcept {
  mathematical_ecology_executor_receipt receipt{};
  if (!organ::valid_mathematical_foundation(mount.canonical) ||
      !organ::valid_mathematical_foundation(mount.reordered) ||
      mount.canonical_body_seed == 0 || mount.reordered_body_seed == 0 ||
      mount.canonical_body_seed == mount.reordered_body_seed) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = mathematical_ecology_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = mathematical_ecology_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  mathematical_ecology_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = mathematical_ecology_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.canonical, 0, sizeof(event::resident_mathematical_ecology)) != cudaSuccess ||
      cudaMemset(storage.reordered, 0, sizeof(event::resident_mathematical_ecology)) != cudaSuccess ||
      cudaMemset(storage.resident, 0, sizeof(mathematical_ecology_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0, sizeof(mathematical_ecology_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = mathematical_ecology_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_mathematical_ecology_mount(storage.mount, storage.canonical, storage.reordered,
          storage.resident) != cudaSuccess ||
      launch_mathematical_ecology_reconstruction(storage.mount, storage.canonical,
          storage.reordered, storage.resident) != cudaSuccess ||
      launch_mathematical_ecology_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = mathematical_ecology_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  const std::uint64_t resident_bytes = sizeof(mathematical_ecology_mount) +
      sizeof(event::resident_mathematical_ecology) * 2U +
      sizeof(mathematical_ecology_observation) * 2U;
  receipt.state = mathematical_ecology_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.source_bytes_after_mount = exact::word{0};
  receipt.launched_threads = exact::word{3};
  receipt.kernel_launches = exact::word{3};
  receipt.host_semantic_events = exact::word{0};
  receipt.logical.read_support = exact::word{observation.canonical.declaration_count};
  receipt.logical.change_support = exact::word{0};
  receipt.logical.alternatives_retained =
      exact::word{observation.canonical.transport_alternatives};
  receipt.logical.obstructions_retained = exact::word{2};
  receipt.logical.reservations_consumed = exact::word{0};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
