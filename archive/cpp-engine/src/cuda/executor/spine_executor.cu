#include <cstddef>
#include <cstdint>
#include <limits>

#include <cuda_runtime.h>

#include <holonics/apparatus/spine_executor.hpp>

namespace holonics::apparatus {
namespace {

__global__ void spine_deed_kernel(
    const exact::spine_deed_input* inputs,
    exact::spine_deed_output* outputs,
    std::size_t count) {
  const std::size_t slot =
      static_cast<std::size_t>(blockIdx.x) * static_cast<std::size_t>(blockDim.x) +
      static_cast<std::size_t>(threadIdx.x);
  if (slot < count) {
    outputs[slot] = body::execute_spine_deed(inputs[slot]);
  }
}

[[nodiscard]] calibrated_integer_interval resident_interval(std::uint64_t value) noexcept {
  return calibrated_integer_interval{
      telemetry_status::calibrated_interval,
      exact::word{value},
      exact::word{value},
      exact::word{1}};
}

}  // namespace

exact_executor_receipt execute_spine_deeds(spine_deed_batch batch) noexcept {
  exact_executor_receipt receipt{};
  if (batch.inputs == nullptr || batch.outputs == nullptr || batch.count == 0) {
    return receipt;
  }
  constexpr std::size_t input_width = sizeof(exact::spine_deed_input);
  constexpr std::size_t output_width = sizeof(exact::spine_deed_output);
  if (batch.count > std::numeric_limits<std::size_t>::max() / input_width ||
      batch.count > std::numeric_limits<std::size_t>::max() / output_width) {
    receipt.state = executor_status::invalid_aperture;
    return receipt;
  }

  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);

  // Physical reservation only. The persistent standing surface is a value in the
  // kernel frame, so the per-thread stack is sized for it explicitly rather than
  // left to a default that would refuse the deed.
  if (cudaDeviceSetLimit(cudaLimitStackSize, 16384) != cudaSuccess) {
    receipt.state = executor_status::device_unavailable;
    return receipt;
  }

  const std::size_t input_bytes = batch.count * input_width;
  const std::size_t output_bytes = batch.count * output_width;
  exact::spine_deed_input* device_inputs = nullptr;
  exact::spine_deed_output* device_outputs = nullptr;
  if (cudaMalloc(&device_inputs, input_bytes) != cudaSuccess ||
      cudaMalloc(&device_outputs, output_bytes) != cudaSuccess) {
    if (device_inputs != nullptr) {
      static_cast<void>(cudaFree(device_inputs));
    }
    if (device_outputs != nullptr) {
      static_cast<void>(cudaFree(device_outputs));
    }
    receipt.state = executor_status::allocation_refused;
    return receipt;
  }

  if (cudaMemcpy(device_inputs, batch.inputs, input_bytes, cudaMemcpyHostToDevice) !=
      cudaSuccess) {
    static_cast<void>(cudaFree(device_inputs));
    static_cast<void>(cudaFree(device_outputs));
    receipt.state = executor_status::transfer_refused;
    return receipt;
  }

  constexpr std::size_t block_width = 64;
  const std::size_t grid_width = (batch.count + block_width - 1) / block_width;
  spine_deed_kernel<<<static_cast<unsigned>(grid_width), static_cast<unsigned>(block_width)>>>(
      device_inputs, device_outputs, batch.count);
  if (cudaGetLastError() != cudaSuccess) {
    static_cast<void>(cudaFree(device_inputs));
    static_cast<void>(cudaFree(device_outputs));
    receipt.state = executor_status::launch_refused;
    return receipt;
  }
  if (cudaDeviceSynchronize() != cudaSuccess) {
    static_cast<void>(cudaFree(device_inputs));
    static_cast<void>(cudaFree(device_outputs));
    receipt.state = executor_status::synchronization_refused;
    return receipt;
  }
  const cudaError_t returning = cudaMemcpy(
      batch.outputs, device_outputs, output_bytes, cudaMemcpyDeviceToHost);
  static_cast<void>(cudaFree(device_inputs));
  static_cast<void>(cudaFree(device_outputs));
  if (returning != cudaSuccess) {
    receipt.state = executor_status::transfer_refused;
    return receipt;
  }

  receipt.state = executor_status::returned;
  receipt.bytes_to_device = exact::word{static_cast<std::uint64_t>(input_bytes)};
  receipt.bytes_from_device = exact::word{static_cast<std::uint64_t>(output_bytes)};
  receipt.launched_threads = exact::word{static_cast<std::uint64_t>(grid_width * block_width)};
  receipt.logical.read_support = exact::word{static_cast<std::uint64_t>(batch.count)};
  receipt.logical.change_support = exact::word{static_cast<std::uint64_t>(batch.count)};
  receipt.physical.resident_bytes = resident_interval(
      static_cast<std::uint64_t>(input_bytes + output_bytes));
  return receipt;
}

}  // namespace holonics::apparatus
