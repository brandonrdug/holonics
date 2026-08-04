#include <new>

#include <holonics/apparatus/lean_checker_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void stage_checker(const lean_checker_mount* mount,
    event::resident_checker_current* current,
    event::checker_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    ::new (static_cast<void*>(current)) event::resident_checker_current{
        mount->body_seed, mount->regions, mount->mathematical_morphology,
        mount->codec_morphology};
    observation->stage = current->stage(mount->source, *observation);
  }
}

__global__ void resume_checker(const event::checker_raw_return* returned,
    event::resident_checker_current* current,
    event::checker_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    static_cast<void>(current->resume(*returned, *observation));
  }
}

__global__ void observe_checker(const event::checker_observation* resident,
    event::checker_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_lean_checker_stage(const lean_checker_mount* mount,
    event::resident_checker_current* current,
    event::checker_observation* observation) noexcept {
  stage_checker<<<1, 1>>>(mount, current, observation);
  return cudaGetLastError();
}

cudaError_t launch_lean_checker_resume(const event::checker_raw_return* returned,
    event::resident_checker_current* current,
    event::checker_observation* observation) noexcept {
  resume_checker<<<1, 1>>>(returned, current, observation);
  return cudaGetLastError();
}

cudaError_t launch_lean_checker_observe(const event::checker_observation* resident,
    event::checker_observation* returned) noexcept {
  observe_checker<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
