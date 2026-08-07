#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/boundary_condensation_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void boundary_condensation_mount_kernel(const boundary_condensation_mount* mount,
    event::resident_condensation* body) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(body)) event::resident_condensation{
      mount->program, mount->body_regions};
}

__global__ void boundary_condensation_advance_kernel(event::resident_condensation* body) {
  if (blockIdx.x != 0 || threadIdx.x != 0 || !body->admitted()) { return; }
  body->apply_history(0);
  body->apply_history(1);
  body->refine_family();
  body->apply_history(2);
  body->apply_history(3);
  body->finish();
}

__global__ void boundary_condensation_observe_kernel(
    const event::resident_condensation* body,
    boundary_condensation_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->semantic = body->observation();
}

}  // namespace

cudaError_t launch_boundary_condensation_mount(const boundary_condensation_mount* mount,
    event::resident_condensation* body) noexcept {
  boundary_condensation_mount_kernel<<<1, 1>>>(mount, body);
  return cudaGetLastError();
}

cudaError_t launch_boundary_condensation_advance(event::resident_condensation* body) noexcept {
  boundary_condensation_advance_kernel<<<1, 1>>>(body);
  return cudaGetLastError();
}

cudaError_t launch_boundary_condensation_observe(const event::resident_condensation* body,
    boundary_condensation_observation* observation) noexcept {
  boundary_condensation_observe_kernel<<<1, 1>>>(body, observation);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
