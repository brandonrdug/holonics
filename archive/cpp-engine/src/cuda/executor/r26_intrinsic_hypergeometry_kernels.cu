#include <new>

#include <holonics/apparatus/intrinsic_hypergeometry_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_intrinsic(const intrinsic_hypergeometry_mount* mount,
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_intrinsic_hypergeometry{
      mount->foundation, mount->inherited, observation->predecessor_remount};
}

__global__ void derive_phase_sources(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::intrinsic_case_capacity) { return; }
  organ::intrinsic_hypergeometry_detail::derive_phase(
      mount->foundation, static_cast<std::uint8_t>(threadIdx.x), observation->inquiry);
}

__global__ void derive_variation_source(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::intrinsic_hypergeometry_detail::derive_variation(
        mount->foundation, observation->inquiry);
  }
}

__global__ void derive_cm_source(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::intrinsic_hypergeometry_detail::derive_cm(mount->foundation, observation->inquiry);
  }
}

__global__ void carry_phase_sections(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::intrinsic_case_capacity) { return; }
  organ::intrinsic_hypergeometry_detail::carry_phase(
      mount->foundation, static_cast<std::uint8_t>(threadIdx.x), observation->inquiry);
}

__global__ void derive_changed_source(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::intrinsic_hypergeometry_detail::derive_phase_incidence(
        mount->changed_foundation, 2, observation->changed_case);
  }
}

__global__ void carry_changed_section(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::intrinsic_hypergeometry_detail::form_chronology(mount->changed_foundation,
        observation->inquiry.local_system, observation->changed_case);
  }
}

__global__ void aggregate_intrinsic(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  organ::intrinsic_hypergeometry_detail::close(
      mount->foundation, mount->question, observation->inquiry);
  const auto& baseline = observation->inquiry.cases[2];
  const auto& changed = observation->changed_case;
  observation->changed_sensitive = changed.exact &&
      baseline.presentation.first == changed.presentation.first &&
      baseline.presentation.second != changed.presentation.second &&
      baseline.vertex_count != changed.vertex_count && baseline.lcm != changed.lcm &&
      organ::intrinsic_hypergeometry_detail::unequal_transitions(baseline, changed) &&
      organ::intrinsic_hypergeometry_detail::unequal_return(baseline, changed);
  observation->inquiry.controls.changed_source_sensitive = observation->changed_sensitive;
}

__global__ void form_intrinsic(event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    static_cast<void>(production->form(*observation));
  }
}

__global__ void resume_intrinsic(const event::checker_raw_return* returned,
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    static_cast<void>(production->resume(*returned, *observation));
  }
}

__global__ void rest_remount_intrinsic(event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_rest_record* rest,
    event::intrinsic_hypergeometry_rest_record* handoff,
    event::intrinsic_hypergeometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest); if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_intrinsic_hypergeometry{
      *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_intrinsic(
    const event::intrinsic_hypergeometry_observation* resident,
    event::intrinsic_hypergeometry_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_intrinsic_hypergeometry_mount(const intrinsic_hypergeometry_mount* mount,
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  mount_intrinsic<<<1,1>>>(mount, production, observation); return cudaGetLastError();
}
cudaError_t launch_intrinsic_phase_sources(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  derive_phase_sources<<<1,organ::intrinsic_case_capacity>>>(mount, observation);
  return cudaGetLastError();
}
cudaError_t launch_intrinsic_nonphase_sources(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  derive_variation_source<<<1,1>>>(mount, observation);
  auto state = cudaGetLastError(); if (state != cudaSuccess) { return state; }
  derive_cm_source<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_intrinsic_phase_transport(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  carry_phase_sections<<<1,organ::intrinsic_case_capacity>>>(mount, observation);
  return cudaGetLastError();
}
cudaError_t launch_intrinsic_changed_source(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  derive_changed_source<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_intrinsic_changed_transport(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  carry_changed_section<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_intrinsic_aggregate(const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  aggregate_intrinsic<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_intrinsic_form(event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  form_intrinsic<<<1,1>>>(production, observation); return cudaGetLastError();
}
cudaError_t launch_intrinsic_resume(const event::checker_raw_return* returned,
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  resume_intrinsic<<<1,1>>>(returned, production, observation); return cudaGetLastError();
}
cudaError_t launch_intrinsic_rest_remount(event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_rest_record* rest,
    event::intrinsic_hypergeometry_rest_record* handoff,
    event::intrinsic_hypergeometry_observation* observation) noexcept {
  rest_remount_intrinsic<<<1,1>>>(production, rest, handoff, observation);
  return cudaGetLastError();
}
cudaError_t launch_intrinsic_observe(
    const event::intrinsic_hypergeometry_observation* resident,
    event::intrinsic_hypergeometry_observation* returned) noexcept {
  observe_intrinsic<<<1,1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
