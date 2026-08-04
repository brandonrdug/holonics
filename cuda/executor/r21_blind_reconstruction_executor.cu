#include <cuda_runtime.h>

#include <holonics/apparatus/blind_reconstruction_resident.hpp>

namespace holonics::apparatus {
namespace {

struct blind_storage final {
  blind_reconstruction_mount* mount{};
  event::resident_blind_reconstruction* production{};
  event::blind_reconstruction_rest_record* rest{};
  event::blind_reconstruction_rest_record* handoff{};
  event::blind_reconstruction_observation* resident{};
  event::blind_reconstruction_observation* returned{};
  event::checker_raw_return* code_raw{};
  event::checker_raw_return* moment_raw{};
};

void release(blind_storage& storage) noexcept {
  if (storage.mount != nullptr) { static_cast<void>(cudaFree(storage.mount)); }
  if (storage.production != nullptr) { static_cast<void>(cudaFree(storage.production)); }
  if (storage.rest != nullptr) { static_cast<void>(cudaFree(storage.rest)); }
  if (storage.handoff != nullptr) { static_cast<void>(cudaFree(storage.handoff)); }
  if (storage.resident != nullptr) { static_cast<void>(cudaFree(storage.resident)); }
  if (storage.returned != nullptr) { static_cast<void>(cudaFree(storage.returned)); }
  if (storage.code_raw != nullptr) { static_cast<void>(cudaFree(storage.code_raw)); }
  if (storage.moment_raw != nullptr) { static_cast<void>(cudaFree(storage.moment_raw)); }
  storage = {};
}

[[nodiscard]] bool allocate(blind_storage& storage) noexcept {
  return cudaMalloc(&storage.mount, sizeof(blind_reconstruction_mount)) == cudaSuccess &&
      cudaMalloc(&storage.production, sizeof(event::resident_blind_reconstruction)) == cudaSuccess &&
      cudaMalloc(&storage.rest, sizeof(event::blind_reconstruction_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.handoff, sizeof(event::blind_reconstruction_rest_record)) == cudaSuccess &&
      cudaMalloc(&storage.resident, sizeof(event::blind_reconstruction_observation)) == cudaSuccess &&
      cudaMalloc(&storage.returned, sizeof(event::blind_reconstruction_observation)) == cudaSuccess &&
      cudaMalloc(&storage.code_raw, sizeof(event::checker_raw_return)) == cudaSuccess &&
      cudaMalloc(&storage.moment_raw, sizeof(event::checker_raw_return)) == cudaSuccess;
}

[[nodiscard]] calibrated_integer_interval interval(std::uint64_t value) noexcept {
  return {telemetry_status::calibrated_interval, exact::word{value}, exact::word{value},
      exact::word{1}};
}

[[nodiscard]] bool initialize(const blind_reconstruction_mount& mount,
    blind_storage& storage) noexcept {
  return cudaMemset(storage.production, 0, sizeof(event::resident_blind_reconstruction)) ==
          cudaSuccess &&
      cudaMemset(storage.rest, 0, sizeof(event::blind_reconstruction_rest_record)) == cudaSuccess &&
      cudaMemset(storage.handoff, 0, sizeof(event::blind_reconstruction_rest_record)) == cudaSuccess &&
      cudaMemset(storage.resident, 0, sizeof(event::blind_reconstruction_observation)) == cudaSuccess &&
      cudaMemset(storage.returned, 0, sizeof(event::blind_reconstruction_observation)) == cudaSuccess &&
      cudaMemset(storage.code_raw, 0, sizeof(event::checker_raw_return)) == cudaSuccess &&
      cudaMemset(storage.moment_raw, 0, sizeof(event::checker_raw_return)) == cudaSuccess &&
      cudaMemcpy(storage.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) == cudaSuccess;
}

}  // namespace

blind_reconstruction_executor_receipt execute_blind_reconstruction(
    const blind_reconstruction_mount& mount, const blind_checker_configuration& process,
    event::blind_reconstruction_observation& observation,
    event::blind_reconstruction_rest_record& handoff) noexcept {
  blind_reconstruction_executor_receipt receipt{};
  if (!organ::blind_reconstruction_detail::valid_foundation(mount.foundation) ||
      mount.question.identity.value() == 0 || mount.question.receiver.value() == 0 ||
      mount.question.material.value() == 0 ||
      mount.inherited.integrity != event::regular_singular_rest_integrity(mount.inherited)) {
    return receipt;
  }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = blind_reconstruction_executor_status::device_unavailable; return receipt;
  }
  int major = 0;
  int minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) {
    receipt.state = blind_reconstruction_executor_status::device_unavailable; return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  blind_storage storage{};
  if (!allocate(storage)) {
    release(storage); receipt.state = blind_reconstruction_executor_status::allocation_refused;
    return receipt;
  }
  if (!initialize(mount, storage)) {
    release(storage); receipt.state = blind_reconstruction_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_blind_mount(storage.mount, storage.production, storage.resident) != cudaSuccess ||
      launch_blind_code(storage.mount, storage.resident) != cudaSuccess ||
      launch_blind_pairs(storage.mount, storage.resident) != cudaSuccess ||
      launch_blind_moments(storage.mount, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(storage); receipt.state = blind_reconstruction_executor_status::reconstruction_refused;
    return receipt;
  }
  if (launch_blind_form_code(storage.mount, storage.production, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.resident, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess || !observation.inquiry.theory_formed ||
      observation.code.checker_stage != event::checker_stage_status::exact) {
    release(storage); receipt.state = blind_reconstruction_executor_status::code_formation_refused;
    return receipt;
  }
  event::checker_raw_return code_raw{};
  const lean_source_view code_source{observation.code.formal.passage,
      observation.code.formal.identity, observation.code.formal.bytes,
      observation.code.formal.byte_count};
  receipt.code_process = run_lean_checker_source(
      code_source, observation.code.outbound, process.code, code_raw);
  if (!receipt.code_process.returned()) {
    release(storage); receipt.state = blind_reconstruction_executor_status::code_process_refused;
    return receipt;
  }
  if (cudaMemcpy(storage.code_raw, &code_raw, sizeof(code_raw), cudaMemcpyHostToDevice) !=
          cudaSuccess ||
      launch_blind_resume_code(storage.code_raw, storage.production, storage.resident) !=
          cudaSuccess || cudaDeviceSynchronize() != cudaSuccess ||
      launch_blind_form_moment(storage.production, storage.resident) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.resident, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess ||
      observation.code.typed.state != event::checker_return_status::accepted ||
      observation.moment.checker_stage != event::checker_stage_status::exact) {
    release(storage); receipt.state = blind_reconstruction_executor_status::code_return_refused;
    return receipt;
  }
  event::checker_raw_return moment_raw{};
  const lean_source_view moment_source{observation.moment.formal.passage,
      observation.moment.formal.identity, observation.moment.formal.bytes,
      observation.moment.formal.byte_count};
  receipt.moment_process = run_lean_checker_source(
      moment_source, observation.moment.outbound, process.moment, moment_raw);
  if (!receipt.moment_process.returned()) {
    release(storage); receipt.state = blind_reconstruction_executor_status::moment_process_refused;
    return receipt;
  }
  if (cudaMemcpy(storage.moment_raw, &moment_raw, sizeof(moment_raw), cudaMemcpyHostToDevice) !=
          cudaSuccess ||
      launch_blind_resume_moment(storage.moment_raw, storage.production, storage.resident) !=
          cudaSuccess || cudaDeviceSynchronize() != cudaSuccess) {
    release(storage); receipt.state = blind_reconstruction_executor_status::moment_return_refused;
    return receipt;
  }
  if (launch_blind_rest_remount(storage.production, storage.rest, storage.handoff,
          storage.resident) != cudaSuccess ||
      launch_blind_observe(storage.resident, storage.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, storage.returned, sizeof(observation),
          cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&handoff, storage.handoff, sizeof(handoff),
          cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(storage); receipt.state = blind_reconstruction_executor_status::rest_refused;
    return receipt;
  }
  release(storage);
  if (observation.moment.typed.state != event::checker_return_status::accepted ||
      !observation.rest.returned || !observation.remount.same_body ||
      !observation.remount.theories_preserved || !observation.handoff.returned ||
      !observation.final_can_continue) {
    receipt.state = blind_reconstruction_executor_status::rest_refused; return receipt;
  }
  const std::uint64_t resident_bytes = sizeof(blind_reconstruction_mount) +
      sizeof(event::resident_blind_reconstruction) +
      sizeof(event::blind_reconstruction_rest_record) * 2U +
      sizeof(event::blind_reconstruction_observation) * 2U +
      sizeof(event::checker_raw_return) * 2U;
  receipt.state = blind_reconstruction_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount) + sizeof(code_raw) + sizeof(moment_raw)};
  receipt.bytes_from_device = exact::word{sizeof(observation) * 3U + sizeof(handoff)};
  receipt.resident_bytes = exact::word{resident_bytes};
  receipt.kernel_launches = exact::word{10};
  receipt.launched_threads = exact::word{16};
  receipt.code_threads = exact::word{4};
  receipt.moment_threads = exact::word{5};
  receipt.host_semantic_events = exact::word{0};
  receipt.released_solution_reads = exact::word{0};
  receipt.logical = {exact::word{133}, exact::word{10}, exact::word{32},
      exact::word{2}, exact::word{2}};
  receipt.physical.resident_bytes = interval(resident_bytes);
  return receipt;
}

}  // namespace holonics::apparatus
