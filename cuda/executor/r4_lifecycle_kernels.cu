#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/body_lifecycle_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void open_body(
    const body_lifecycle_input* input,
    body::continuing_body* standing,
    event::live_pending* pending,
    event::lifecycle_output* output) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  auto* live = ::new (static_cast<void*>(standing)) body::continuing_body{
      input->request.owner_seed, input->regions};
  output->predecessor = event::observe(*live);
  output->resume_state = event::open(*live, input->request, pending, output->outbound);
}

__global__ void resume_commit_rest(
    const event::deed_return* returned,
    body::continuing_body* standing,
    event::live_pending* pending,
    event::live_delta* delta,
    body::rest_record* rest,
    event::lifecycle_output* output) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  output->resume_state = event::resume(*pending, *returned, delta);
  if (output->resume_state != event::lifecycle_status::exact) { return; }
  output->delta = delta->receipt();
  output->commit = event::commit(*standing, *delta);
  output->successor = event::observe(*standing);
  output->rest = standing->rest(*rest);
  output->exterior_returns = 1;
}

__global__ void remount_body(
    const body::rest_record* rest,
    body::continuing_body* standing,
    event::lifecycle_output* output) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  auto* live = ::new (static_cast<void*>(standing)) body::continuing_body{
      body::continuing_body::remount(*rest, output->remount)};
  output->remounted = event::observe(*live);
  output->source_replays = output->remount.source_replay_count;
}

}  // namespace

cudaError_t launch_body_open(
    const body_lifecycle_input* input,
    body::continuing_body* standing,
    event::live_pending* pending,
    event::lifecycle_output* output) noexcept {
  open_body<<<1, 1>>>(input, standing, pending, output);
  return cudaGetLastError();
}

cudaError_t launch_body_resume_rest(
    const event::deed_return* returned,
    body::continuing_body* standing,
    event::live_pending* pending,
    event::live_delta* delta,
    body::rest_record* rest,
    event::lifecycle_output* output) noexcept {
  resume_commit_rest<<<1, 1>>>(returned, standing, pending, delta, rest, output);
  return cudaGetLastError();
}

cudaError_t launch_body_remount(
    const body::rest_record* rest,
    body::continuing_body* standing,
    event::lifecycle_output* output) noexcept {
  remount_body<<<1, 1>>>(rest, standing, output);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
