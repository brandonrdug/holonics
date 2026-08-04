#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/generative_math_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_generative_current(
    const generative_math_mount* mount,
    event::resident_generative_math_current* current,
    generative_math_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(current)) event::resident_generative_math_current{
      mount->foundation, mount->body_seed, mount->regions, true};
  observation->mount_obstruction = current->obstruction();
}

__global__ void form_generated_passage(
    const generative_math_mount* mount,
    event::resident_generative_math_current* current,
    generative_math_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->returned = current->generate(mount->question);
}

__global__ void observe_generated_passage(
    const generative_math_observation* resident,
    generative_math_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_generative_math_mount(
    const generative_math_mount* mount,
    event::resident_generative_math_current* current,
    generative_math_observation* observation) noexcept {
  mount_generative_current<<<1, 1>>>(mount, current, observation);
  return cudaGetLastError();
}

cudaError_t launch_generative_math_form(
    const generative_math_mount* mount,
    event::resident_generative_math_current* current,
    generative_math_observation* observation) noexcept {
  form_generated_passage<<<1, 1>>>(mount, current, observation);
  return cudaGetLastError();
}

cudaError_t launch_generative_math_observe(
    const generative_math_observation* resident,
    generative_math_observation* returned) noexcept {
  observe_generated_passage<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
