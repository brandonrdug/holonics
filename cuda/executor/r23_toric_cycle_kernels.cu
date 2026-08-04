#include <new>

#include <holonics/apparatus/toric_cycle_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_toric(const toric_cycle_mount* mount,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_toric_cycle{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void derive_toric(const toric_cycle_mount* mount,
    event::toric_cycle_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  organ::toric_cycle_detail::derive(mount->foundation, observation->inquiry);
}

__global__ void form_toric_passage(const toric_cycle_mount* mount,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(mount->question, *observation));
}

__global__ void resume_toric_passage(const event::checker_raw_return* returned,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_toric(event::resident_toric_cycle* production,
    event::toric_cycle_rest_record* rest, event::toric_cycle_rest_record* handoff,
    event::toric_cycle_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_toric_cycle{
      *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_toric(const event::toric_cycle_observation* resident,
    event::toric_cycle_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_toric_mount(const toric_cycle_mount* mount,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) noexcept {
  mount_toric<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_toric_derive(const toric_cycle_mount* mount,
    event::toric_cycle_observation* observation) noexcept {
  derive_toric<<<1, 1>>>(mount, observation); return cudaGetLastError();
}

cudaError_t launch_toric_form(const toric_cycle_mount* mount,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) noexcept {
  form_toric_passage<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_toric_resume(const event::checker_raw_return* returned,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) noexcept {
  resume_toric_passage<<<1, 1>>>(returned, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_toric_rest_remount(event::resident_toric_cycle* production,
    event::toric_cycle_rest_record* rest, event::toric_cycle_rest_record* handoff,
    event::toric_cycle_observation* observation) noexcept {
  rest_remount_toric<<<1, 1>>>(production, rest, handoff, observation);
  return cudaGetLastError();
}

cudaError_t launch_toric_observe(const event::toric_cycle_observation* resident,
    event::toric_cycle_observation* returned) noexcept {
  observe_toric<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
