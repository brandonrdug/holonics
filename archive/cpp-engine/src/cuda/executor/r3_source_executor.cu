#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/source_topology_resident.hpp>

namespace holonics::apparatus {
namespace {

[[nodiscard]] calibrated_integer_interval exact_interval(std::uint64_t value) noexcept {
  return calibrated_integer_interval{
      telemetry_status::calibrated_interval,
      exact::word{value},
      exact::word{value},
      exact::word{1}};
}

void release_storage(
    codec::encoded_source_environment* environment,
    structure::resident_marked_population* populations,
    receiver::resident_projection_chart* charts,
    chunk_boundary_summary* summaries,
    source_mount_accumulator* accumulators,
    source_topology_output* output) noexcept {
  if (environment != nullptr) { static_cast<void>(cudaFree(environment)); }
  if (populations != nullptr) { static_cast<void>(cudaFree(populations)); }
  if (charts != nullptr) { static_cast<void>(cudaFree(charts)); }
  if (summaries != nullptr) { static_cast<void>(cudaFree(summaries)); }
  if (accumulators != nullptr) { static_cast<void>(cudaFree(accumulators)); }
  if (output != nullptr) { static_cast<void>(cudaFree(output)); }
}

}  // namespace

source_topology_executor_receipt execute_source_topology(
    codec::source_environment&& environment,
    source_topology_output& output) noexcept {
  source_topology_executor_receipt receipt{};
  if (!environment.admitted() || environment.encoded().source_count == 0 ||
      environment.encoded().byte_count == 0) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = source_topology_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = source_topology_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);

  constexpr std::size_t environment_bytes = sizeof(codec::encoded_source_environment);
  constexpr std::size_t population_bytes =
      sizeof(structure::resident_marked_population) * codec::source_variant_capacity;
  constexpr std::size_t chart_bytes =
      sizeof(receiver::resident_projection_chart) * codec::source_variant_capacity;
  constexpr std::size_t summary_bytes =
      sizeof(chunk_boundary_summary) * codec::source_chunk_capacity;
  constexpr std::size_t accumulator_bytes =
      sizeof(source_mount_accumulator) * codec::source_variant_capacity;
  constexpr std::size_t output_bytes = sizeof(source_topology_output);
  codec::encoded_source_environment* device_environment = nullptr;
  structure::resident_marked_population* device_populations = nullptr;
  receiver::resident_projection_chart* device_charts = nullptr;
  chunk_boundary_summary* device_summaries = nullptr;
  source_mount_accumulator* device_accumulators = nullptr;
  source_topology_output* device_output = nullptr;
  if (cudaMalloc(&device_environment, environment_bytes) != cudaSuccess ||
      cudaMalloc(&device_populations, population_bytes) != cudaSuccess ||
      cudaMalloc(&device_charts, chart_bytes) != cudaSuccess ||
      cudaMalloc(&device_summaries, summary_bytes) != cudaSuccess ||
      cudaMalloc(&device_accumulators, accumulator_bytes) != cudaSuccess ||
      cudaMalloc(&device_output, output_bytes) != cudaSuccess) {
    release_storage(device_environment, device_populations, device_charts,
        device_summaries, device_accumulators, device_output);
    receipt.state = source_topology_executor_status::allocation_refused;
    return receipt;
  }
  if (cudaMemset(device_populations, 0, population_bytes) != cudaSuccess ||
      cudaMemset(device_charts, 0, chart_bytes) != cudaSuccess ||
      cudaMemset(device_summaries, 0, summary_bytes) != cudaSuccess ||
      cudaMemset(device_accumulators, 0, accumulator_bytes) != cudaSuccess ||
      cudaMemset(device_output, 0, output_bytes) != cudaSuccess ||
      cudaMemcpy(device_environment, &environment.encoded(), environment_bytes,
          cudaMemcpyHostToDevice) != cudaSuccess) {
    release_storage(device_environment, device_populations, device_charts,
        device_summaries, device_accumulators, device_output);
    receipt.state = source_topology_executor_status::transfer_refused;
    return receipt;
  }
  const std::uint8_t query_face = environment.encoded().query_face;
  const std::uint8_t obstruction_face = environment.encoded().obstruction_face;
  const std::uint64_t query_occurrence = environment.encoded().query_occurrence;
  if (launch_source_foundation(device_environment, device_populations, device_charts,
          device_summaries, device_accumulators, device_output) != cudaSuccess) {
    release_storage(device_environment, device_populations, device_charts,
        device_summaries, device_accumulators, device_output);
    receipt.state = source_topology_executor_status::launch_refused;
    return receipt;
  }
  if (launch_source_admission(device_environment, device_populations,
          device_accumulators) != cudaSuccess) {
    release_storage(device_environment, device_populations, device_charts,
        device_summaries, device_accumulators, device_output);
    receipt.state = source_topology_executor_status::launch_refused;
    return receipt;
  }
  if (cudaDeviceSynchronize() != cudaSuccess) {
    release_storage(device_environment, device_populations, device_charts,
        device_summaries, device_accumulators, device_output);
    receipt.state = source_topology_executor_status::synchronization_refused;
    return receipt;
  }
  environment.detach();
  static_cast<void>(cudaFree(device_environment));
  device_environment = nullptr;
  if (launch_detached_navigation(device_populations, device_charts,
          device_accumulators, device_output, query_face, obstruction_face,
          query_occurrence) != cudaSuccess) {
    release_storage(device_environment, device_populations, device_charts,
        device_summaries, device_accumulators, device_output);
    receipt.state = source_topology_executor_status::launch_refused;
    return receipt;
  }
  if (cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&output, device_output, output_bytes, cudaMemcpyDeviceToHost) != cudaSuccess) {
    release_storage(device_environment, device_populations, device_charts,
        device_summaries, device_accumulators, device_output);
    receipt.state = source_topology_executor_status::transfer_refused;
    return receipt;
  }
  release_storage(device_environment, device_populations, device_charts,
      device_summaries, device_accumulators, device_output);

  constexpr std::uint64_t block_threads =
      ((codec::source_chunk_capacity + 127U) / 128U) * 128U;
  constexpr std::uint64_t admission_threads =
      ((structure::marked_occurrence_capacity + 127U) / 128U) * 128U;
  receipt.state = source_topology_executor_status::returned;
  receipt.bytes_to_device = exact::word{environment_bytes};
  receipt.bytes_from_device = exact::word{output_bytes};
  receipt.resident_structure_bytes = exact::word{
      population_bytes + summary_bytes + accumulator_bytes};
  receipt.resident_chart_bytes = exact::word{chart_bytes};
  receipt.launched_threads = exact::word{4U + block_threads * 2U + admission_threads + 4U};
  receipt.kernel_launches = exact::word{5};
  receipt.logical.read_support = exact::word{
      static_cast<std::uint64_t>(output.variants[0].navigation.preimage.projection_words_touched) +
      output.variants[0].navigation.preimage.occurrences_touched +
      output.variants[0].navigation.support.occurrence_count};
  receipt.logical.change_support = exact::word{
      static_cast<std::uint64_t>(output.variants[0].population.occurrence_count) +
      output.variants[0].population.relation_count};
  receipt.physical.resident_bytes = exact_interval(
      population_bytes + chart_bytes + summary_bytes + accumulator_bytes + output_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
