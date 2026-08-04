#include <cstddef>
#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/receiver_geometry_resident.hpp>

#include "r7_geometry_law.cuh"

namespace holonics::apparatus {
namespace {

__global__ void receiver_geometry_mount_kernel(const receiver_geometry_mount* mount,
    current::resident_weave* current,
    receiver::resident_geometry* receiver) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(current)) current::resident_weave{mount->current};
  ::new (static_cast<void*>(receiver)) receiver::resident_geometry{mount->receiver};
  const auto current_state = current::validate_weave_program(mount->current);
  if (current_state != current::weave_obstruction::none) {
    current->set_validation(current_state);
  }
}

__global__ void receiver_geometry_advance_kernel(current::resident_weave* current,
    receiver::resident_geometry* receiver) {
  if (blockIdx.x != 0 || current->validation() != current::weave_obstruction::none ||
      !receiver->admitted()) {
    return;
  }
  __shared__ bool committed;
  for (std::uint16_t layer = 0; layer < current->program().layer_count; ++layer) {
    r6_device::apply_layer(*current, layer, committed);
    if (!committed) { return; }
  }
  if (threadIdx.x == 0) {
    current->begin_resource_return();
    committed = current->commit_resource_return();
  }
  __syncthreads();
  if (!committed) { return; }
  if (threadIdx.x < current->program().cell_count) {
    current->apply_resource_cell(threadIdx.x);
  }
  __syncthreads();
  r7_device::apply_geometry(*current, *receiver);
}

__global__ void receiver_geometry_observe_kernel(const current::resident_weave* current,
    const receiver::resident_geometry* receiver,
    receiver_geometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->current_predecessor = current::predecessor_snapshot(current->program());
  observation->current_successor = current->standing();
  observation->receiver = receiver->observation();
  observation->current_returned = current->validation() == current::weave_obstruction::none &&
      current->committed_layers() == current->program().layer_count + 1U;
}

}  // namespace

cudaError_t launch_receiver_geometry_mount(const receiver_geometry_mount* mount,
    current::resident_weave* current,
    receiver::resident_geometry* receiver) noexcept {
  receiver_geometry_mount_kernel<<<1, 1>>>(mount, current, receiver);
  return cudaGetLastError();
}

cudaError_t launch_receiver_geometry_advance(current::resident_weave* current,
    receiver::resident_geometry* receiver) noexcept {
  receiver_geometry_advance_kernel<<<1, current::weave_cell_capacity>>>(current, receiver);
  return cudaGetLastError();
}

cudaError_t launch_receiver_geometry_observe(const current::resident_weave* current,
    const receiver::resident_geometry* receiver,
    receiver_geometry_observation* observation) noexcept {
  receiver_geometry_observe_kernel<<<1, 1>>>(current, receiver, observation);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
