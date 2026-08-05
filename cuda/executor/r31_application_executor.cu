#include <holonics/apparatus/cultivated_current_set.hpp>
#include <holonics/apparatus/cultivated_organ_executor.hpp>

namespace holonics::apparatus {
namespace {
struct application_storage final {
  cultivated_application_mount *mount{}; unsigned char *resident{};
  event::cultivated_application_observation *observation{};
  event::cultivated_application_observation *returned{};
  event::checker_raw_return *raw{}; event::cultivated_organ_rest_record *rest{};
  event::cultivated_organ_rest_record *handoff{};
};
void release_one(void *value) noexcept { if (value) static_cast<void>(cudaFree(value)); }
void release(application_storage &s) noexcept {
  release_one(s.handoff); release_one(s.rest); release_one(s.raw); release_one(s.returned);
  release_one(s.observation); release_one(s.resident); release_one(s.mount); s = {};
}
[[nodiscard]] bool allocate(application_storage &s) noexcept {
  return cudaMalloc(reinterpret_cast<void **>(&s.mount), sizeof(*s.mount)) == cudaSuccess &&
      cudaMalloc(reinterpret_cast<void **>(&s.resident), sizeof(event::resident_cultivated_organs)) == cudaSuccess &&
      cudaMalloc(reinterpret_cast<void **>(&s.observation), sizeof(*s.observation)) == cudaSuccess &&
      cudaMalloc(reinterpret_cast<void **>(&s.returned), sizeof(*s.returned)) == cudaSuccess &&
      cudaMalloc(reinterpret_cast<void **>(&s.raw), sizeof(*s.raw)) == cudaSuccess &&
      cudaMalloc(reinterpret_cast<void **>(&s.rest), sizeof(*s.rest)) == cudaSuccess &&
      cudaMalloc(reinterpret_cast<void **>(&s.handoff), sizeof(*s.handoff)) == cudaSuccess;
}
[[nodiscard]] bool initialize(const cultivated_application_mount &mount,
    application_storage &s) noexcept {
  return cudaMemcpy(s.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) == cudaSuccess &&
      cudaMemset(s.resident, 0, sizeof(event::resident_cultivated_organs)) == cudaSuccess &&
      cudaMemset(s.observation, 0, sizeof(*s.observation)) == cudaSuccess &&
      cudaMemset(s.returned, 0, sizeof(*s.returned)) == cudaSuccess &&
      cudaMemset(s.raw, 0, sizeof(*s.raw)) == cudaSuccess &&
      cudaMemset(s.rest, 0, sizeof(*s.rest)) == cudaSuccess && cudaMemset(s.handoff, 0, sizeof(*s.handoff)) == cudaSuccess;
}
[[nodiscard]] bool device(cultivated_executor_receipt &receipt) noexcept {
  int count = 0, major = 0, minor = 0;
  if (cudaGetDeviceCount(&count) != cudaSuccess || count <= 0 || cudaSetDevice(0) != cudaSuccess ||
      cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) != cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) != cudaSuccess) return false;
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor); return true;
}
[[nodiscard]] bool valid_structures(const organ::heldout_structure_bundle &x) noexcept {
  return x.star.metadata.parsed && x.walk.metadata.parsed && x.carrier.metadata.parsed &&
      x.graded.metadata.parsed && x.star.last_branch_count == 10 && x.walk.step_count == 4 &&
      x.carrier.maximum_horizon == 8 && x.graded.generators == 2;
}
}  // namespace

cultivated_executor_receipt execute_cultivated_application(
    const cultivated_application_mount &mount, const lean_process_configuration &process,
    event::cultivated_application_observation &observation,
    event::cultivated_organ_rest_record &handoff) noexcept {
  cultivated_executor_receipt receipt{};
  if (mount.inherited.integrity != event::cultivated_organ_rest_integrity(mount.inherited) ||
      mount.inherited.applied || !valid_structures(mount.structures)) return receipt;
  if (!device(receipt)) { receipt.state = cultivated_executor_status::device_unavailable; return receipt; }
  application_storage s{};
  if (!allocate(s)) { release(s); receipt.state = cultivated_executor_status::allocation_refused; return receipt; }
  if (!initialize(mount, s) || launch_application_mount(s.mount, s.resident, s.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(s); receipt.state = cultivated_executor_status::transfer_refused; return receipt;
  }
  cultivated_current_set currents{}; bool exact = open_cultivated_currents(currents);
  for (std::uint8_t i = 0; exact && i < organ::cultivation_family_count; ++i)
    exact = launch_application_source(s.mount,
        reinterpret_cast<event::resident_cultivated_organs *>(s.resident), s.observation,
        i, currents.currents[i]) == cudaSuccess;
  exact = exact && join_cultivated_currents(currents); close_cultivated_currents(currents);
  if (!exact || launch_application_close(s.mount, s.observation) != cudaSuccess ||
      launch_application_form(reinterpret_cast<event::resident_cultivated_organs *>(s.resident), s.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess || cudaMemcpy(&observation, s.observation, sizeof(observation),
      cudaMemcpyDeviceToHost) != cudaSuccess || !observation.inquiry.theory_formed) {
    release(s); receipt.state = cultivated_executor_status::formation_refused; return receipt;
  }
  event::checker_raw_return raw{};
  const lean_source_view source{observation.passage.formal.passage, observation.passage.formal.identity,
      observation.passage.formal.bytes, observation.passage.formal.byte_count};
  receipt.checker = run_lean_checker_source(source, observation.passage.outbound, process, raw);
  if (!receipt.checker.returned()) { release(s); receipt.state = cultivated_executor_status::checker_process_refused; return receipt; }
  if (cudaMemcpy(s.raw, &raw, sizeof(raw), cudaMemcpyHostToDevice) != cudaSuccess ||
      launch_application_resume(s.raw, reinterpret_cast<event::resident_cultivated_organs *>(s.resident), s.observation) != cudaSuccess ||
      launch_application_rest(reinterpret_cast<event::resident_cultivated_organs *>(s.resident), s.rest, s.handoff, s.observation) != cudaSuccess ||
      launch_application_observe(s.observation, s.returned) != cudaSuccess || cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, s.returned, sizeof(observation), cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&handoff, s.handoff, sizeof(handoff), cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(s); receipt.state = cultivated_executor_status::checker_return_refused; return receipt;
  }
  const std::uint64_t bytes = sizeof(mount) + sizeof(event::resident_cultivated_organs) +
      2U*sizeof(observation) + sizeof(raw) + 2U*sizeof(handoff); release(s);
  if (observation.passage.typed.state != event::checker_return_status::accepted ||
      !observation.rest.returned || !observation.remount.application_preserved ||
      !observation.handoff.returned || !handoff.applied)
    { receipt.state = cultivated_executor_status::rest_refused; return receipt; }
  receipt.state = cultivated_executor_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(mount)+sizeof(raw)};
  receipt.bytes_from_device = exact::word{sizeof(observation)+sizeof(handoff)};
  receipt.resident_bytes = exact::word{bytes}; receipt.kernel_launches = exact::word{10};
  receipt.launched_threads = exact::word{10}; receipt.semantic_threads = exact::word{8};
  receipt.source_currents = exact::word{4}; receipt.dependency_barriers = exact::word{1};
  receipt.physical.resident_bytes = {telemetry_status::calibrated_interval,
      exact::word{bytes}, exact::word{bytes}, exact::word{1}};
  return receipt;
}

}  // namespace holonics::apparatus
