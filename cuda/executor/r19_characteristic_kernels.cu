#include <new>

#include <holonics/apparatus/characteristic_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_characteristic(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_characteristic{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void probe_characteristic(const characteristic_mount* mount,
    event::characteristic_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::characteristic_case_capacity) { return; }
  const auto slot = static_cast<std::uint16_t>(threadIdx.x);
  observation->inquiry.cases[slot] = organ::form_characteristic_case(
      mount->foundation, slot);
}

__global__ void form_characteristic(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(mount->question, *observation));
}

__global__ void resume_characteristic(const event::checker_raw_return* returned,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_characteristic(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_rest_record* rest,
    event::characteristic_rest_record* handoff,
    event::characteristic_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_characteristic{
      mount->foundation, *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_characteristic(const event::characteristic_observation* resident,
    event::characteristic_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_characteristic_mount(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) noexcept {
  mount_characteristic<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_characteristic_cases(const characteristic_mount* mount,
    event::characteristic_observation* observation) noexcept {
  probe_characteristic<<<1, organ::characteristic_case_capacity>>>(mount, observation);
  return cudaGetLastError();
}

cudaError_t launch_characteristic_form(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) noexcept {
  form_characteristic<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_characteristic_resume(const event::checker_raw_return* returned,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) noexcept {
  resume_characteristic<<<1, 1>>>(returned, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_characteristic_rest_remount(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_rest_record* rest,
    event::characteristic_rest_record* handoff,
    event::characteristic_observation* observation) noexcept {
  rest_remount_characteristic<<<1, 1>>>(mount, production, rest, handoff, observation);
  return cudaGetLastError();
}

cudaError_t launch_characteristic_observe(
    const event::characteristic_observation* resident,
    event::characteristic_observation* returned) noexcept {
  observe_characteristic<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
