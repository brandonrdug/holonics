#include <new>

#include <holonics/apparatus/geometry_inquiry_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_geometry_inquiry(const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_geometry_inquiry{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void probe_geometry_inquiry(const geometry_inquiry_mount* mount,
    event::geometry_inquiry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::geometry_inquiry_probe_capacity) { return; }
  const auto slot = static_cast<std::uint16_t>(threadIdx.x);
  observation->inquiry.probes[slot] = organ::form_geometry_probe(mount->foundation, slot);
}

__global__ void form_geometry_inquiry(const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(mount->question, *observation));
}

__global__ void resume_geometry_inquiry(const event::checker_raw_return* returned,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_geometry_inquiry(const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_rest_record* rest,
    event::geometry_inquiry_rest_record* handoff,
    event::geometry_inquiry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_geometry_inquiry{
      mount->foundation, *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_geometry_inquiry(
    const event::geometry_inquiry_observation* resident,
    event::geometry_inquiry_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_geometry_inquiry_mount(const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) noexcept {
  mount_geometry_inquiry<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_geometry_inquiry_probes(const geometry_inquiry_mount* mount,
    event::geometry_inquiry_observation* observation) noexcept {
  probe_geometry_inquiry<<<1, 32>>>(mount, observation);
  return cudaGetLastError();
}

cudaError_t launch_geometry_inquiry_form(const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) noexcept {
  form_geometry_inquiry<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_geometry_inquiry_resume(const event::checker_raw_return* returned,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) noexcept {
  resume_geometry_inquiry<<<1, 1>>>(returned, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_geometry_inquiry_rest_remount(const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_rest_record* rest,
    event::geometry_inquiry_rest_record* handoff,
    event::geometry_inquiry_observation* observation) noexcept {
  rest_remount_geometry_inquiry<<<1, 1>>>(mount, production, rest, handoff, observation);
  return cudaGetLastError();
}

cudaError_t launch_geometry_inquiry_observe(
    const event::geometry_inquiry_observation* resident,
    event::geometry_inquiry_observation* returned) noexcept {
  observe_geometry_inquiry<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
