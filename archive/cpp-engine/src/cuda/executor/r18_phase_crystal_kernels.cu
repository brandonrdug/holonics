#include <new>

#include <holonics/apparatus/phase_crystal_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_phase_crystal(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_phase_crystal{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void probe_phase_crystal(const phase_crystal_mount* mount,
    event::phase_crystal_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::phase_crystal_case_capacity) { return; }
  const auto slot = static_cast<std::uint16_t>(threadIdx.x);
  observation->inquiry.cases[slot] = organ::form_phase_crystal_case(mount->foundation, slot);
}

__global__ void form_phase_crystal(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(mount->question, *observation));
}

__global__ void resume_phase_crystal(const event::checker_raw_return* returned,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_phase_crystal(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_rest_record* rest,
    event::phase_crystal_rest_record* handoff,
    event::phase_crystal_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_phase_crystal{
      mount->foundation, *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_phase_crystal(const event::phase_crystal_observation* resident,
    event::phase_crystal_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_phase_crystal_mount(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) noexcept {
  mount_phase_crystal<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_phase_crystal_cases(const phase_crystal_mount* mount,
    event::phase_crystal_observation* observation) noexcept {
  probe_phase_crystal<<<1, organ::phase_crystal_case_capacity>>>(mount, observation);
  return cudaGetLastError();
}

cudaError_t launch_phase_crystal_form(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) noexcept {
  form_phase_crystal<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_phase_crystal_resume(const event::checker_raw_return* returned,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) noexcept {
  resume_phase_crystal<<<1, 1>>>(returned, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_phase_crystal_rest_remount(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_rest_record* rest,
    event::phase_crystal_rest_record* handoff,
    event::phase_crystal_observation* observation) noexcept {
  rest_remount_phase_crystal<<<1, 1>>>(mount, production, rest, handoff, observation);
  return cudaGetLastError();
}

cudaError_t launch_phase_crystal_observe(
    const event::phase_crystal_observation* resident,
    event::phase_crystal_observation* returned) noexcept {
  observe_phase_crystal<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
