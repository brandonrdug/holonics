#include <new>

#include <holonics/apparatus/regular_singular_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_regular_singular(const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_regular_singular{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void probe_regular_singular_charts(const regular_singular_mount* mount,
    event::regular_singular_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::regular_singular_chart_capacity) { return; }
  const auto slot = static_cast<std::uint16_t>(threadIdx.x);
  observation->inquiry.charts[slot] =
      organ::regular_singular_detail::form_chart(mount->foundation, slot);
}

__global__ void probe_regular_singular_terms(const regular_singular_mount* mount,
    event::regular_singular_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::regular_singular_term_capacity) { return; }
  const auto slot = static_cast<std::uint16_t>(threadIdx.x);
  observation->inquiry.terms[slot] =
      organ::regular_singular_detail::form_term(mount->foundation, slot);
}

__global__ void form_regular_singular(const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(mount->question, *observation));
}

__global__ void resume_regular_singular(const event::checker_raw_return* returned,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_regular_singular(const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_rest_record* rest,
    event::regular_singular_rest_record* handoff,
    event::regular_singular_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_regular_singular{
      mount->foundation, *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_regular_singular(
    const event::regular_singular_observation* resident,
    event::regular_singular_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_regular_singular_mount(const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) noexcept {
  mount_regular_singular<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_regular_singular_charts(const regular_singular_mount* mount,
    event::regular_singular_observation* observation) noexcept {
  probe_regular_singular_charts<<<1, organ::regular_singular_chart_capacity>>>(
      mount, observation);
  return cudaGetLastError();
}

cudaError_t launch_regular_singular_terms(const regular_singular_mount* mount,
    event::regular_singular_observation* observation) noexcept {
  probe_regular_singular_terms<<<1, organ::regular_singular_term_capacity>>>(
      mount, observation);
  return cudaGetLastError();
}

cudaError_t launch_regular_singular_form(const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) noexcept {
  form_regular_singular<<<1, 1>>>(mount, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_regular_singular_resume(const event::checker_raw_return* returned,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) noexcept {
  resume_regular_singular<<<1, 1>>>(returned, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_regular_singular_rest_remount(const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_rest_record* rest,
    event::regular_singular_rest_record* handoff,
    event::regular_singular_observation* observation) noexcept {
  rest_remount_regular_singular<<<1, 1>>>(mount, production, rest, handoff, observation);
  return cudaGetLastError();
}

cudaError_t launch_regular_singular_observe(
    const event::regular_singular_observation* resident,
    event::regular_singular_observation* returned) noexcept {
  observe_regular_singular<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
