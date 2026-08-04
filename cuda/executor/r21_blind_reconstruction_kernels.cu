#include <new>

#include <holonics/apparatus/blind_reconstruction_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_blind(const blind_reconstruction_mount* mount,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_blind_reconstruction{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void form_code_population(const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  organ::blind_code_detail::form_code_population(
      mount->foundation.code, observation->inquiry.code);
}

__global__ void form_pair_populations(const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::blind_pair_capacity) { return; }
  const auto slot = static_cast<std::uint8_t>(threadIdx.x);
  organ::blind_code_detail::form_pair_incidence(mount->foundation.code,
      observation->inquiry.code, slot, observation->inquiry.pairs[slot]);
}

__global__ void form_moment_populations(const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::blind_moment_case_capacity) { return; }
  const auto slot = static_cast<std::uint8_t>(threadIdx.x);
  organ::blind_moment_detail::form_moment_root(
      mount->foundation.moments.cases[slot], slot, observation->inquiry.moments[slot]);
}

__global__ void form_code_passage(const blind_reconstruction_mount* mount,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form_code(mount->question, *observation));
}

__global__ void resume_code_passage(const event::checker_raw_return* returned,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume_code(*returned, *observation));
}

__global__ void form_moment_passage(event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form_moment(*observation));
}

__global__ void resume_moment_passage(const event::checker_raw_return* returned,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume_moment(*returned, *observation));
}

__global__ void rest_remount_blind(event::resident_blind_reconstruction* production,
    event::blind_reconstruction_rest_record* rest,
    event::blind_reconstruction_rest_record* handoff,
    event::blind_reconstruction_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_blind_reconstruction{
      *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_blind(const event::blind_reconstruction_observation* resident,
    event::blind_reconstruction_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_blind_mount(const blind_reconstruction_mount* mount,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept {
  mount_blind<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_blind_code(const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) noexcept {
  form_code_population<<<1, 1>>>(mount, observation); return cudaGetLastError();
}

cudaError_t launch_blind_pairs(const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) noexcept {
  form_pair_populations<<<1, organ::blind_pair_capacity>>>(mount, observation);
  return cudaGetLastError();
}

cudaError_t launch_blind_moments(const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) noexcept {
  form_moment_populations<<<1, organ::blind_moment_case_capacity>>>(mount, observation);
  return cudaGetLastError();
}

cudaError_t launch_blind_form_code(const blind_reconstruction_mount* mount,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept {
  form_code_passage<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_blind_resume_code(const event::checker_raw_return* returned,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept {
  resume_code_passage<<<1, 1>>>(returned, production, observation); return cudaGetLastError();
}

cudaError_t launch_blind_form_moment(event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept {
  form_moment_passage<<<1, 1>>>(production, observation); return cudaGetLastError();
}

cudaError_t launch_blind_resume_moment(const event::checker_raw_return* returned,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept {
  resume_moment_passage<<<1, 1>>>(returned, production, observation); return cudaGetLastError();
}

cudaError_t launch_blind_rest_remount(event::resident_blind_reconstruction* production,
    event::blind_reconstruction_rest_record* rest,
    event::blind_reconstruction_rest_record* handoff,
    event::blind_reconstruction_observation* observation) noexcept {
  rest_remount_blind<<<1, 1>>>(production, rest, handoff, observation);
  return cudaGetLastError();
}

cudaError_t launch_blind_observe(const event::blind_reconstruction_observation* resident,
    event::blind_reconstruction_observation* returned) noexcept {
  observe_blind<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
