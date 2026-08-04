#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/generative_math_resident.hpp>

namespace holonics::apparatus {
namespace {

struct generative_math_storage final {
  generative_math_mount* mount{};
  event::resident_generative_math_current* current{};
  generative_math_observation* resident{};
  generative_math_observation* returned{};
};

void release(generative_math_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.current != nullptr) { static_cast<void>(cudaFree(storage.current)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  storage = {};
}

[[nodiscard]] bool allocate(generative_math_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(generative_math_mount)) == cudaSuccess &&
      cudaMalloc(&storage.current, sizeof(event::resident_generative_math_current)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(generative_math_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(generative_math_observation)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value},
      exact::word{value}, exact::word{1}};
}

}  // namespace

generative_math_executor_receipt execute_generative_math(
    const generative_math_mount& mount, generative_math_observation& observation) noexcept {
  generative_math_executor_receipt receipt{};
  if (!organ::valid_generative_foundation(mount.foundation) || mount.body_seed == 0 ||
      mount.question.identity.value() == 0 || mount.question.receiver.value() == 0) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = generative_math_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = generative_math_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  generative_math_storage storage{};
  if (!allocate(storage)) {
    release(storage); receipt.state = generative_math_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.current, 0, sizeof(event::resident_generative_math_current)) != cudaSuccess ||
      cudaMemset(storage.resident, 0, sizeof(generative_math_observation)) != cudaSuccess ||
      cudaMemset(storage.returned, 0, sizeof(generative_math_observation)) != cudaSuccess ||
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage); receipt.state = generative_math_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_generative_math_mount(storage.mount, storage.current, storage.resident) != cudaSuccess ||
      launch_generative_math_form(storage.mount, storage.current, storage.resident) != cudaSuccess ||
      launch_generative_math_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = generative_math_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  const std::uint64_t resident_bytes = sizeof(generative_math_mount) +
      sizeof(event::resident_generative_math_current) + sizeof(generative_math_observation) * 2U;
  receipt.state = generative_math_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)};
  receipt.bytes_from_device = exact::word{sizeof(observation)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.mounted_answer_bytes = exact::word{0};
  receipt.external_checker_calls = exact::word{0};
  receipt.launched_threads = exact::word{3};
  receipt.kernel_launches = exact::word{3};
  receipt.host_semantic_events = exact::word{0};
  receipt.logical.read_support = exact::word{2};
  receipt.logical.change_support = exact::word{3};
  receipt.logical.alternatives_retained = exact::word{1};
  receipt.logical.obstructions_retained = exact::word{1};
  receipt.logical.reservations_consumed = exact::word{1};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
