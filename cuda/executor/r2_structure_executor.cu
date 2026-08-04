#include <cstddef>
#include <cstdint>
#include <limits>
#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/structure_executor.hpp>
#include <holonics/structure/structure_deed.hpp>

namespace holonics::apparatus {
namespace {

__global__ void r2_admit_complex_kernel(
    const structure::structure_case* inputs,
    structure::resident_complex* complexes,
    structure::structure_output* outputs,
    std::size_t count) {
  const std::size_t slot =
      static_cast<std::size_t>(blockIdx.x) * static_cast<std::size_t>(blockDim.x) +
      static_cast<std::size_t>(threadIdx.x);
  if (slot < count) {
    structure::resident_complex* complex =
        ::new (static_cast<void*>(complexes + slot))
            structure::resident_complex(inputs[slot].owner_seed);
    structure::admit_structure_case(*complex, inputs[slot], outputs[slot]);
  }
}

__global__ void r2_continue_complex_kernel(
    const structure::structure_case* inputs,
    structure::resident_complex* complexes,
    structure::structure_output* outputs,
    std::size_t count) {
  const std::size_t slot =
      static_cast<std::size_t>(blockIdx.x) * static_cast<std::size_t>(blockDim.x) +
      static_cast<std::size_t>(threadIdx.x);
  if (slot < count) {
    structure::continue_structure_case(complexes[slot], inputs[slot], outputs[slot]);
  }
}

[[nodiscard]] calibrated_integer_interval exact_interval(std::uint64_t value) noexcept {
  return calibrated_integer_interval{
      telemetry_status::calibrated_interval,
      exact::word{value},
      exact::word{value},
      exact::word{1}};
}

void release_device_storage(
    structure::structure_case* inputs,
    structure::resident_complex* complexes,
    structure::structure_output* outputs) noexcept {
  if (inputs != nullptr) {
    static_cast<void>(cudaFree(inputs));
  }
  if (complexes != nullptr) {
    static_cast<void>(cudaFree(complexes));
  }
  if (outputs != nullptr) {
    static_cast<void>(cudaFree(outputs));
  }
}

}  // namespace

structure_executor_receipt execute_structure_deeds(structure_batch batch) noexcept {
  structure_executor_receipt receipt{};
  if (batch.inputs == nullptr || batch.outputs == nullptr || batch.count == 0) {
    return receipt;
  }
  constexpr std::size_t input_size = sizeof(structure::structure_case);
  constexpr std::size_t complex_size = sizeof(structure::resident_complex);
  constexpr std::size_t output_size = sizeof(structure::structure_output);
  if (batch.count > std::numeric_limits<std::size_t>::max() / input_size ||
      batch.count > std::numeric_limits<std::size_t>::max() / complex_size ||
      batch.count > std::numeric_limits<std::size_t>::max() / output_size) {
    return receipt;
  }

  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = structure_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = structure_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);

  const std::size_t input_bytes = batch.count * input_size;
  const std::size_t complex_bytes = batch.count * complex_size;
  const std::size_t output_bytes = batch.count * output_size;
  structure::structure_case* device_inputs = nullptr;
  structure::resident_complex* device_complexes = nullptr;
  structure::structure_output* device_outputs = nullptr;
  if (cudaMalloc(&device_inputs, input_bytes) != cudaSuccess ||
      cudaMalloc(&device_complexes, complex_bytes) != cudaSuccess ||
      cudaMalloc(&device_outputs, output_bytes) != cudaSuccess) {
    release_device_storage(device_inputs, device_complexes, device_outputs);
    receipt.state = structure_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(device_complexes, 0, complex_bytes) != cudaSuccess ||
      cudaMemset(device_outputs, 0, output_bytes) != cudaSuccess) {
    release_device_storage(device_inputs, device_complexes, device_outputs);
    receipt.state = structure_executor_status::transfer_refused;
    return receipt;
  }
  if (cudaMemcpy(device_inputs, batch.inputs, input_bytes, cudaMemcpyHostToDevice) != cudaSuccess) {
    release_device_storage(device_inputs, device_complexes, device_outputs);
    receipt.state = structure_executor_status::transfer_refused;
    return receipt;
  }

  constexpr std::size_t block_width = 128;
  const std::size_t grid_width = (batch.count + block_width - 1) / block_width;
  r2_admit_complex_kernel<<<static_cast<unsigned>(grid_width), static_cast<unsigned>(block_width)>>>(
      device_inputs, device_complexes, device_outputs, batch.count);
  if (cudaGetLastError() != cudaSuccess) {
    release_device_storage(device_inputs, device_complexes, device_outputs);
    receipt.state = structure_executor_status::launch_refused;
    return receipt;
  }
  r2_continue_complex_kernel<<<static_cast<unsigned>(grid_width), static_cast<unsigned>(block_width)>>>(
      device_inputs, device_complexes, device_outputs, batch.count);
  if (cudaGetLastError() != cudaSuccess || cudaDeviceSynchronize() != cudaSuccess) {
    release_device_storage(device_inputs, device_complexes, device_outputs);
    receipt.state = structure_executor_status::synchronization_refused;
    return receipt;
  }
  if (cudaMemcpy(batch.outputs, device_outputs, output_bytes, cudaMemcpyDeviceToHost) != cudaSuccess) {
    release_device_storage(device_inputs, device_complexes, device_outputs);
    receipt.state = structure_executor_status::transfer_refused;
    return receipt;
  }
  release_device_storage(device_inputs, device_complexes, device_outputs);

  receipt.state = structure_executor_status::returned;
  receipt.bytes_to_device = exact::word{static_cast<std::uint64_t>(input_bytes)};
  receipt.bytes_from_device = exact::word{static_cast<std::uint64_t>(output_bytes)};
  receipt.resident_structure_bytes = exact::word{static_cast<std::uint64_t>(complex_bytes)};
  receipt.launched_threads = exact::word{
      static_cast<std::uint64_t>(grid_width * block_width * 2)};
  receipt.kernel_launches = exact::word{2};
  receipt.logical.read_support = exact::word{static_cast<std::uint64_t>(batch.count)};
  receipt.logical.change_support = exact::word{static_cast<std::uint64_t>(batch.count)};
  receipt.physical.resident_bytes = exact_interval(
      static_cast<std::uint64_t>(input_bytes + complex_bytes + output_bytes));
  return receipt;
}

}  // namespace holonics::apparatus
