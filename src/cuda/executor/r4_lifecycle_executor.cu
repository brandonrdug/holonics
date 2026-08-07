#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/body_lifecycle_resident.hpp>

namespace holonics::apparatus {
namespace {

struct device_storage final {
  body_lifecycle_input* input{};
  event::deed_return* returned{};
  body::continuing_body* standing{};
  event::live_pending* pending{};
  event::live_delta* delta{};
  body::rest_record* rest{};
  event::lifecycle_output* output{};
};

void release(device_storage& storage) noexcept {
  if (storage.input != nullptr) { static_cast<void>(cudaFree(storage.input)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  if (storage.standing != nullptr) { static_cast<void>(cudaFree(storage.standing)); }
  if (storage.pending != nullptr) { static_cast<void>(cudaFree(storage.pending)); }
  if (storage.delta != nullptr) { static_cast<void>(cudaFree(storage.delta)); }
  if (storage.rest != nullptr) { static_cast<void>(cudaFree(storage.rest)); }
  if (storage.output != nullptr) { static_cast<void>(cudaFree(storage.output)); }
  storage = {};
}

[[nodiscard]] bool allocate(device_storage& storage) noexcept {
  return cudaMalloc(&storage.input, sizeof(body_lifecycle_input)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(event::deed_return)) == cudaSuccess &&
      cudaMalloc(&storage.standing, sizeof(body::continuing_body)) == cudaSuccess &&
      cudaMalloc(&storage.pending, sizeof(event::live_pending)) == cudaSuccess &&
      cudaMalloc(&storage.delta, sizeof(event::live_delta)) == cudaSuccess &&
      cudaMalloc(&storage.rest, sizeof(body::rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.output, sizeof(event::lifecycle_output)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval exact_interval(std::uint64_t value) noexcept {
  return calibrated_integer_interval{telemetry_status::calibrated_interval,
      exact::word{value}, exact::word{value}, exact::word{1}};
}

}  // namespace

body_lifecycle_executor_receipt execute_body_lifecycle(
    const body_lifecycle_input& input,
    event::lifecycle_output& output) noexcept {
  body_lifecycle_executor_receipt receipt{};
  if (input.request.region >= body::live_region_capacity) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = body_lifecycle_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = body_lifecycle_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  device_storage storage{};
  if (!allocate(storage)) {
    release(storage);
    receipt.state = body_lifecycle_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(storage.standing, 0, sizeof(body::continuing_body)) != cudaSuccess ||
      cudaMemset(storage.pending, 0, sizeof(event::live_pending)) != cudaSuccess ||
      cudaMemset(storage.delta, 0, sizeof(event::live_delta)) != cudaSuccess ||
      cudaMemset(storage.rest, 0, sizeof(body::rest_record)) != cudaSuccess ||
      cudaMemset(storage.output, 0, sizeof(event::lifecycle_output)) != cudaSuccess ||
      cudaMemcpy(storage.input, &input, sizeof(input), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = body_lifecycle_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_body_open(storage.input, storage.standing, storage.pending, storage.output) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&output, storage.output, sizeof(output), cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = body_lifecycle_executor_status::synchronization_refused;
    return receipt;
  }
  const event::deed_return returned{output.outbound.predecessor, output.outbound.event,
      output.outbound.expected_return_port, output.outbound.lineage + 1U, input.returned_payload};
  if (cudaMemcpy(storage.returned, &returned, sizeof(returned), cudaMemcpyHostToDevice) != cudaSuccess ||
      launch_body_resume_rest(storage.returned, storage.standing, storage.pending,
          storage.delta, storage.rest, storage.output) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(storage);
    receipt.state = body_lifecycle_executor_status::synchronization_refused;
    return receipt;
  }
  body::rest_record host_rest{};
  if (cudaMemcpy(&host_rest, storage.rest, sizeof(host_rest), cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = body_lifecycle_executor_status::transfer_refused;
    return receipt;
  }
  static_cast<void>(cudaFree(storage.input)); storage.input = nullptr;
  static_cast<void>(cudaFree(storage.returned)); storage.returned = nullptr;
  static_cast<void>(cudaFree(storage.standing)); storage.standing = nullptr;
  static_cast<void>(cudaFree(storage.pending)); storage.pending = nullptr;
  static_cast<void>(cudaFree(storage.delta)); storage.delta = nullptr;
  static_cast<void>(cudaFree(storage.rest)); storage.rest = nullptr;
  if (cudaMalloc(&storage.standing, sizeof(body::continuing_body)) != cudaSuccess ||
      cudaMalloc(&storage.rest, sizeof(body::rest_record)) != cudaSuccess ||
      cudaMemset(storage.standing, 0, sizeof(body::continuing_body)) != cudaSuccess ||
      cudaMemcpy(storage.rest, &host_rest, sizeof(host_rest), cudaMemcpyHostToDevice) != cudaSuccess) {
    release(storage);
    receipt.state = body_lifecycle_executor_status::allocation_refused;
    return receipt;
  }
  if (launch_body_remount(storage.rest, storage.standing, storage.output) != cudaSuccess ||
      launch_body_adversarial(storage.output) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&output, storage.output, sizeof(output), cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage);
    receipt.state = body_lifecycle_executor_status::synchronization_refused;
    return receipt;
  }
  release(storage);
  constexpr std::uint64_t resident_bytes = sizeof(body::continuing_body) +
      sizeof(event::live_pending) + sizeof(event::live_delta) + sizeof(body::rest_record) +
      sizeof(event::lifecycle_output);
  receipt.state = body_lifecycle_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(input) + sizeof(returned) + sizeof(host_rest)};
  receipt.bytes_from_device = exact::word{sizeof(output) * 2U + sizeof(host_rest)};
  receipt.resident_body_bytes = exact::word{resident_bytes};
  receipt.launched_threads = exact::word{4};
  receipt.kernel_launches = exact::word{4};
  receipt.logical.read_support = exact::word{1};
  receipt.logical.change_support = exact::word{1};
  receipt.logical.alternatives_retained = exact::word{5};
  receipt.logical.obstructions_retained = exact::word{1};
  receipt.logical.reservations_consumed = exact::word{1};
  receipt.physical.resident_bytes = exact_interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
