#include <new>

#include <holonics/apparatus/algebraic_variation_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_variation(const algebraic_variation_mount* mount,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_algebraic_variation{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void derive_variation(const algebraic_variation_mount* mount,
    event::algebraic_variation_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->inquiry = organ::algebraic_variation_detail::derive(
      mount->foundation, mount->question);
}

__global__ void form_variation(const algebraic_variation_mount* mount,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(mount->question, *observation));
}

__global__ void resume_variation(const event::checker_raw_return* returned,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_variation(event::resident_algebraic_variation* production,
    event::algebraic_variation_rest_record* rest,
    event::algebraic_variation_rest_record* handoff,
    event::algebraic_variation_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_algebraic_variation{
      *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_variation(const event::algebraic_variation_observation* resident,
    event::algebraic_variation_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_variation_mount(const algebraic_variation_mount* mount,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) noexcept {
  mount_variation<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}
cudaError_t launch_variation_derive(const algebraic_variation_mount* mount,
    event::algebraic_variation_observation* observation) noexcept {
  derive_variation<<<1, 1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_variation_form(const algebraic_variation_mount* mount,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) noexcept {
  form_variation<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}
cudaError_t launch_variation_resume(const event::checker_raw_return* returned,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) noexcept {
  resume_variation<<<1, 1>>>(returned, production, observation); return cudaGetLastError();
}
cudaError_t launch_variation_rest_remount(event::resident_algebraic_variation* production,
    event::algebraic_variation_rest_record* rest,
    event::algebraic_variation_rest_record* handoff,
    event::algebraic_variation_observation* observation) noexcept {
  rest_remount_variation<<<1, 1>>>(production, rest, handoff, observation);
  return cudaGetLastError();
}
cudaError_t launch_variation_observe(
    const event::algebraic_variation_observation* resident,
    event::algebraic_variation_observation* returned) noexcept {
  observe_variation<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
