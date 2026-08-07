#include <new>

#include <holonics/apparatus/causal_linear_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_causal_linear(const causal_linear_mount* mount,
    event::resident_causal_linear* production,
    event::causal_linear_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_causal_linear{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void derive_causal_linear_phase(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::derive_source(mount->foundation, 0, observation->inquiry);
  }
}

__global__ void derive_causal_linear_cm(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::derive_source(mount->foundation, 1, observation->inquiry);
  }
}

__global__ void derive_causal_linear_toric(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::derive_source(mount->foundation, 2, observation->inquiry);
  }
}

__global__ void derive_causal_linear_variation(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::derive_source(mount->foundation, 3, observation->inquiry);
  }
}

__global__ void aggregate_causal_linear(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  organ::causal_linear_detail::close(mount->foundation, mount->question,
      observation->inquiry);
}

__global__ void derive_causal_linear_spectral_control(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::control_spectral(
        mount->foundation.card, observation->inquiry.controls);
  }
}

__global__ void derive_causal_linear_kernel_control(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::control_kernel(
        mount->foundation.card, observation->inquiry.controls);
  }
}

__global__ void derive_causal_linear_conjugacy_control(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::control_conjugacy(
        mount->foundation.card, observation->inquiry.controls);
  }
}

__global__ void derive_causal_linear_field_control(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::causal_linear_detail::control_coefficient_field(
        mount->foundation.card, observation->inquiry.controls);
  }
}

__global__ void form_causal_linear(event::resident_causal_linear* production,
    event::causal_linear_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->form(*observation));
}

__global__ void resume_causal_linear(const event::checker_raw_return* returned,
    event::resident_causal_linear* production,
    event::causal_linear_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_remount_causal_linear(event::resident_causal_linear* production,
    event::causal_linear_rest_record* rest, event::causal_linear_rest_record* handoff,
    event::causal_linear_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_causal_linear{
      *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_causal_linear(const event::causal_linear_observation* resident,
    event::causal_linear_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_causal_linear_mount(const causal_linear_mount* mount,
    event::resident_causal_linear* production,
    event::causal_linear_observation* observation) noexcept {
  mount_causal_linear<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}
cudaError_t launch_causal_linear_sources(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) noexcept {
  derive_causal_linear_phase<<<1, 1>>>(mount, observation);
  auto state = cudaGetLastError(); if (state != cudaSuccess) { return state; }
  derive_causal_linear_cm<<<1, 1>>>(mount, observation);
  state = cudaGetLastError(); if (state != cudaSuccess) { return state; }
  derive_causal_linear_toric<<<1, 1>>>(mount, observation);
  state = cudaGetLastError(); if (state != cudaSuccess) { return state; }
  derive_causal_linear_variation<<<1, 1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_causal_linear_controls(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) noexcept {
  derive_causal_linear_spectral_control<<<1, 1>>>(mount, observation);
  auto state = cudaGetLastError(); if (state != cudaSuccess) { return state; }
  derive_causal_linear_kernel_control<<<1, 1>>>(mount, observation);
  state = cudaGetLastError(); if (state != cudaSuccess) { return state; }
  derive_causal_linear_conjugacy_control<<<1, 1>>>(mount, observation);
  state = cudaGetLastError(); if (state != cudaSuccess) { return state; }
  derive_causal_linear_field_control<<<1, 1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_causal_linear_aggregate(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) noexcept {
  aggregate_causal_linear<<<1, 1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_causal_linear_form(event::resident_causal_linear* production,
    event::causal_linear_observation* observation) noexcept {
  form_causal_linear<<<1, 1>>>(production, observation); return cudaGetLastError();
}
cudaError_t launch_causal_linear_resume(const event::checker_raw_return* returned,
    event::resident_causal_linear* production,
    event::causal_linear_observation* observation) noexcept {
  resume_causal_linear<<<1, 1>>>(returned, production, observation); return cudaGetLastError();
}
cudaError_t launch_causal_linear_rest_remount(event::resident_causal_linear* production,
    event::causal_linear_rest_record* rest, event::causal_linear_rest_record* handoff,
    event::causal_linear_observation* observation) noexcept {
  rest_remount_causal_linear<<<1, 1>>>(production, rest, handoff, observation);
  return cudaGetLastError();
}
cudaError_t launch_causal_linear_observe(
    const event::causal_linear_observation* resident,
    event::causal_linear_observation* returned) noexcept {
  observe_causal_linear<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
