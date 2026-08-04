#include <new>

#include <holonics/apparatus/cm_incidence_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_cm(const cm_incidence_mount* mount,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_cm_incidence{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void form_cm_translations(const cm_incidence_mount* mount,
    event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  organ::cm_incidence_detail::form_translations(
      mount->foundation.card, observation->inquiry);
}

__global__ void form_cm_periodic(event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  organ::cm_incidence_detail::form_periodic(observation->inquiry);
}

__global__ void form_cm_window(event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  organ::cm_window_detail::form_window(observation->inquiry);
  organ::cm_window_detail::form_expanded_projection(observation->inquiry);
  organ::cm_window_detail::form_scattering(observation->inquiry);
}

__global__ void form_cm_characteristic(const cm_incidence_mount* mount,
    event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= 2) { return; }
  auto& graph = threadIdx.x == 0 ? observation->inquiry.periodic :
      observation->inquiry.window;
  organ::cm_incidence_detail::form_characteristic(mount->foundation.card, graph);
}

__global__ void form_cm_passage(const cm_incidence_mount* mount,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(mount->question, *observation));
}

__global__ void resume_cm_passage(const event::checker_raw_return* returned,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_cm(event::resident_cm_incidence* production,
    event::cm_incidence_rest_record* rest, event::cm_incidence_rest_record* handoff,
    event::cm_incidence_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_cm_incidence{
      *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_cm(const event::cm_incidence_observation* resident,
    event::cm_incidence_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_cm_mount(const cm_incidence_mount* mount,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) noexcept {
  mount_cm<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_cm_translations(const cm_incidence_mount* mount,
    event::cm_incidence_observation* observation) noexcept {
  form_cm_translations<<<1, 1>>>(mount, observation); return cudaGetLastError();
}

cudaError_t launch_cm_periodic(event::cm_incidence_observation* observation) noexcept {
  form_cm_periodic<<<1, 1>>>(observation); return cudaGetLastError();
}

cudaError_t launch_cm_window(event::cm_incidence_observation* observation) noexcept {
  form_cm_window<<<1, 1>>>(observation); return cudaGetLastError();
}

cudaError_t launch_cm_characteristics(const cm_incidence_mount* mount,
    event::cm_incidence_observation* observation) noexcept {
  form_cm_characteristic<<<1, 2>>>(mount, observation); return cudaGetLastError();
}

cudaError_t launch_cm_form(const cm_incidence_mount* mount,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) noexcept {
  form_cm_passage<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_cm_resume(const event::checker_raw_return* returned,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) noexcept {
  resume_cm_passage<<<1, 1>>>(returned, production, observation); return cudaGetLastError();
}

cudaError_t launch_cm_rest_remount(event::resident_cm_incidence* production,
    event::cm_incidence_rest_record* rest, event::cm_incidence_rest_record* handoff,
    event::cm_incidence_observation* observation) noexcept {
  rest_remount_cm<<<1, 1>>>(production, rest, handoff, observation);
  return cudaGetLastError();
}

cudaError_t launch_cm_observe(const event::cm_incidence_observation* resident,
    event::cm_incidence_observation* returned) noexcept {
  observe_cm<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
