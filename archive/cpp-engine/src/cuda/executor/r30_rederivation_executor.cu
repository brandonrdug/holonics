#include <holonics/apparatus/rederivation_current_set.hpp>
#include <holonics/apparatus/rederivation_executor.hpp>

namespace holonics::apparatus {
namespace {

struct storage final {
  rederivation_mount *mount{};
  unsigned char *production{};
  event::resident_rederivation *resident{};
  event::rederivation_observation *observation{};
  event::rederivation_observation *returned{};
  organ::rederivation_workspace *workspace{};
  event::checker_raw_return *raw{};
  event::rederivation_rest_record *rest{};
  event::rederivation_rest_record *handoff{};
};
void release_one(void *value) noexcept {
  if (value)
    static_cast<void>(cudaFree(value));
}
void release(storage &s) noexcept {
  release_one(s.handoff);
  release_one(s.rest);
  release_one(s.raw);
  release_one(s.workspace);
  release_one(s.returned);
  release_one(s.observation);
  release_one(s.production);
  release_one(s.mount);
  s = {};
}
[[nodiscard]] bool allocate(storage &s) noexcept {
  return cudaMalloc(reinterpret_cast<void **>(&s.mount),
                    sizeof(rederivation_mount)) == cudaSuccess &&
         cudaMalloc(reinterpret_cast<void **>(&s.production),
                    sizeof(event::resident_rederivation)) == cudaSuccess &&
         cudaMalloc(reinterpret_cast<void **>(&s.observation),
                    sizeof(event::rederivation_observation)) == cudaSuccess &&
         cudaMalloc(reinterpret_cast<void **>(&s.returned),
                    sizeof(event::rederivation_observation)) == cudaSuccess &&
         cudaMalloc(reinterpret_cast<void **>(&s.workspace),
                    sizeof(organ::rederivation_workspace)) == cudaSuccess &&
         cudaMalloc(reinterpret_cast<void **>(&s.raw),
                    sizeof(event::checker_raw_return)) == cudaSuccess &&
         cudaMalloc(reinterpret_cast<void **>(&s.rest),
                    sizeof(event::rederivation_rest_record)) == cudaSuccess &&
         cudaMalloc(reinterpret_cast<void **>(&s.handoff),
                    sizeof(event::rederivation_rest_record)) == cudaSuccess;
}
[[nodiscard]] bool initialize(const rederivation_mount &mount,
                              storage &s) noexcept {
  return cudaMemcpy(s.mount, &mount, sizeof(mount), cudaMemcpyHostToDevice) ==
             cudaSuccess &&
         cudaMemset(s.production, 0, sizeof(event::resident_rederivation)) ==
             cudaSuccess &&
         cudaMemset(s.observation, 0,
                    sizeof(event::rederivation_observation)) == cudaSuccess &&
         cudaMemset(s.returned, 0, sizeof(event::rederivation_observation)) ==
             cudaSuccess &&
         cudaMemset(s.workspace, 0, sizeof(organ::rederivation_workspace)) ==
             cudaSuccess &&
         cudaMemset(s.raw, 0, sizeof(event::checker_raw_return)) ==
             cudaSuccess &&
         cudaMemset(s.rest, 0, sizeof(*s.rest)) == cudaSuccess &&
         cudaMemset(s.handoff, 0, sizeof(*s.handoff)) == cudaSuccess;
}
} // namespace

rederivation_executor_receipt
execute_rederivation(const rederivation_mount &mount,
                     const rederivation_process_configuration &process,
                     event::rederivation_observation &observation,
                     organ::rederivation_workspace &workspace,
                     event::rederivation_rest_record &handoff) noexcept {
  rederivation_executor_receipt receipt{};
  if (!organ::rederivation_detail::valid(mount.foundation) ||
      mount.question.identity.value() == 0 ||
      mount.inherited.integrity !=
          event::arithmetic_spectral_rest_integrity(mount.inherited))
    return receipt;
  int count = 0;
  if (cudaGetDeviceCount(&count) != cudaSuccess || count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = rederivation_executor_status::device_unavailable;
    return receipt;
  }
  int major = 0, minor = 0;
  if (cudaDeviceGetAttribute(&major, cudaDevAttrComputeCapabilityMajor, 0) !=
          cudaSuccess ||
      cudaDeviceGetAttribute(&minor, cudaDevAttrComputeCapabilityMinor, 0) !=
          cudaSuccess) {
    receipt.state = rederivation_executor_status::device_unavailable;
    return receipt;
  }
  receipt.device_major = static_cast<std::uint32_t>(major);
  receipt.device_minor = static_cast<std::uint32_t>(minor);
  storage s{};
  if (!allocate(s)) {
    release(s);
    receipt.state = rederivation_executor_status::allocation_refused;
    return receipt;
  }
  s.resident = reinterpret_cast<event::resident_rederivation *>(s.production);
  if (!initialize(mount, s)) {
    release(s);
    receipt.state = rederivation_executor_status::transfer_refused;
    return receipt;
  }
  if (launch_rederivation_mount(s.mount, s.production, s.observation) !=
          cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(s);
    receipt.state = rederivation_executor_status::derivation_refused;
    return receipt;
  }
  rederivation_current_set currents{};
  bool source_returned = open_rederivation_currents(currents);
  if (source_returned)
    source_returned =
        launch_rederivation_matching(s.resident, s.observation, s.workspace,
                                     currents.matching) == cudaSuccess &&
        launch_rederivation_geometry(s.resident, s.observation, s.workspace,
                                     currents.geometry) == cudaSuccess &&
        launch_rederivation_cover(s.resident, s.observation, s.workspace,
                                  currents.cover) == cudaSuccess &&
        join_rederivation_currents(currents);
  close_rederivation_currents(currents);
  if (!source_returned ||
      launch_rederivation_matching_close(s.resident, s.observation,
                                         s.workspace) != cudaSuccess ||
      launch_rederivation_compose(s.resident, s.observation, s.workspace) !=
          cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess) {
    release(s);
    receipt.state = rederivation_executor_status::derivation_refused;
    return receipt;
  }
  if (launch_rederivation_form_foil(s.resident, s.observation) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, s.observation, sizeof(observation),
                 cudaMemcpyDeviceToHost) != cudaSuccess ||
      !observation.inquiry.theory_formed) {
    release(s);
    receipt.state = rederivation_executor_status::foil_formation_refused;
    return receipt;
  }
  event::checker_raw_return foil_raw{};
  const lean_source_view foil_source{
      observation.foil.formal.passage, observation.foil.formal.identity,
      observation.foil.formal.bytes, observation.foil.formal.byte_count};
  receipt.foil_process = run_lean_checker_source(
      foil_source, observation.foil.outbound, process.foil, foil_raw);
  if (!receipt.foil_process.returned()) {
    release(s);
    receipt.state = rederivation_executor_status::foil_process_refused;
    return receipt;
  }
  if (cudaMemcpy(s.raw, &foil_raw, sizeof(foil_raw), cudaMemcpyHostToDevice) !=
          cudaSuccess ||
      launch_rederivation_resume_foil(s.raw, s.resident, s.observation) !=
          cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      launch_rederivation_form_valid(s.resident, s.observation, s.workspace) !=
          cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, s.observation, sizeof(observation),
                 cudaMemcpyDeviceToHost) != cudaSuccess ||
      !observation.foil.expected_rejection) {
    release(s);
    receipt.state = rederivation_executor_status::foil_return_refused;
    return receipt;
  }
  event::checker_raw_return valid_raw{};
  const lean_source_view valid_source{
      observation.passage.formal.passage, observation.passage.formal.identity,
      observation.passage.formal.bytes, observation.passage.formal.byte_count};
  receipt.valid_process = run_lean_checker_source(
      valid_source, observation.passage.outbound, process.valid, valid_raw);
  if (!receipt.valid_process.returned()) {
    release(s);
    receipt.state = rederivation_executor_status::valid_process_refused;
    return receipt;
  }
  if (cudaMemcpy(s.raw, &valid_raw, sizeof(valid_raw),
                 cudaMemcpyHostToDevice) != cudaSuccess ||
      launch_rederivation_resume_valid(s.raw, s.resident, s.observation) !=
          cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      launch_rederivation_rest(s.resident, s.rest, s.handoff, s.observation) !=
          cudaSuccess ||
      launch_rederivation_observe(s.observation, s.returned) != cudaSuccess ||
      cudaDeviceSynchronize() != cudaSuccess ||
      cudaMemcpy(&observation, s.returned, sizeof(observation),
                 cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&workspace, s.workspace, sizeof(workspace),
                 cudaMemcpyDeviceToHost) != cudaSuccess ||
      cudaMemcpy(&handoff, s.handoff, sizeof(handoff),
                 cudaMemcpyDeviceToHost) != cudaSuccess) {
    release(s);
    receipt.state = rederivation_executor_status::valid_return_refused;
    return receipt;
  }
  release(s);
  if (observation.passage.typed.state !=
          event::checker_return_status::accepted ||
      !observation.rest.returned || !observation.remount.same_body ||
      !observation.remount.theory_preserved || !observation.handoff.returned ||
      !observation.final_can_continue) {
    receipt.state = rederivation_executor_status::rest_refused;
    return receipt;
  }
  const std::uint64_t bytes = sizeof(rederivation_mount) +
                              sizeof(event::resident_rederivation) +
                              2U * sizeof(event::rederivation_observation) +
                              sizeof(organ::rederivation_workspace) +
                              2U * sizeof(event::rederivation_rest_record) +
                              sizeof(event::checker_raw_return);
  receipt.state = rederivation_executor_status::returned;
  receipt.bytes_to_device =
      exact::word{sizeof(mount) + 2U * sizeof(event::checker_raw_return)};
  receipt.bytes_from_device = exact::word{2U * sizeof(observation) +
                                          sizeof(workspace) + sizeof(handoff)};
  receipt.resident_bytes = exact::word{bytes};
  receipt.kernel_launches = exact::word{12};
  receipt.launched_threads = exact::word{2'574};
  receipt.semantic_threads = exact::word{2'415};
  receipt.host_semantic_events = exact::word{0};
  receipt.source_currents = exact::word{3};
  receipt.dependency_barriers = exact::word{1};
  receipt.logical = {exact::word{2'401}, exact::word{5'460}, exact::word{70},
                     exact::word{64}, exact::word{4}};
  receipt.physical.resident_bytes = {telemetry_status::calibrated_interval,
                                     exact::word{bytes}, exact::word{bytes},
                                     exact::word{1}};
  return receipt;
}

} // namespace holonics::apparatus
