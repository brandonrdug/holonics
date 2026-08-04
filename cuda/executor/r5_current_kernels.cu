#include <cstddef>
#include <cstdint>
#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/causal_current_resident.hpp>

#include "r5_current_front.cuh"

namespace holonics::apparatus {
namespace {

__global__ void mount_kernel(
    const current::current_mount_batch* mount,
    current::resident_causal_body* bodies,
    current::current_batch_observation* observation) {
  if (blockIdx.x != 0) { return; }
  if (threadIdx.x == 0) { observation->count = mount->count; }
  const std::size_t slot = threadIdx.x;
  if (slot >= mount->count || slot >= current::current_case_capacity) { return; }
  ::new (static_cast<void*>(bodies + slot)) current::resident_causal_body{mount->programs[slot]};
  const auto validation = current::validate_program(mount->programs[slot]);
  if (validation != current::current_obstruction::none) { bodies[slot].obstruct(validation); }
}

__global__ void advance_kernel(
    current::resident_causal_body* bodies,
    const current::current_batch_observation* observation) {
  const std::size_t case_slot = blockIdx.x;
  if (case_slot >= observation->count) { return; }
  auto& body = bodies[case_slot];
  __shared__ std::uint16_t input_count;
  __shared__ std::uint16_t produced;
  __shared__ std::uint64_t occurrence_first;
  for (std::uint16_t frontier = 0; frontier < current::program_front_capacity; ++frontier) {
    if (threadIdx.x == 0) {
      input_count = 0;
      if (body.state() == current::current_status::mounted &&
          frontier < body.program().receiver_front_aperture) {
        r5_device::prepare_front(body, input_count, produced, occurrence_first, frontier);
      }
    }
    __syncthreads();
    if (input_count == 0) { break; }
    if (threadIdx.x < input_count && body.failure() == 0) {
      r5_device::advance_member(body, static_cast<std::uint16_t>(threadIdx.x), occurrence_first);
    }
    __syncthreads();
    if (threadIdx.x == 0) {
      auto& receipt = body.front(frontier);
      body.retain_front_support();
      receipt.read_support = exact::word{body.front_touched_support()};
      receipt.change_support = exact::word{body.front_changed_support()};
      if (body.failure() != 0) {
        body.recover_front();
        receipt.successor = receipt.predecessor;
        receipt.pending_after = 0;
        body.complete_front(0, input_count);
        body.obstruct(static_cast<current::current_obstruction>(body.failure()));
      } else {
        for (std::size_t slot = 0; slot < input_count; ++slot) {
          auto& morphology = body.morphology(body.current(slot).site);
          morphology.passages = exact::word{morphology.passages.value() + 1U};
        }
        const exact::word fold = current::fold_currents(&body.next(0), produced);
        const auto commit = body.commit_front(fold);
        receipt.successor = commit.successor;
        if (commit.state != body::body_change_status::committed) {
          body.complete_front(0, input_count);
          body.obstruct(current::current_obstruction::capacity_refused);
        } else {
          receipt.current_fold = fold;
          receipt.reservations = produced;
          receipt.pending_after = 0;
          body.complete_front(produced, input_count);
          body.publish(produced);
          if (body.open_count() != 0) { body.set_state(current::current_status::open_frontier); }
          else if (produced == 0) { body.set_state(current::current_status::exact_rest); }
          else if (frontier + 1U == body.program().receiver_front_aperture) {
            body.open_with(current::current_obstruction::receiver_aperture);
          }
        }
      }
      r5_device::certify_components(body);
    }
    __syncthreads();
    if (body.state() != current::current_status::mounted) { break; }
  }
}

__global__ void observe_kernel(
    const current::resident_causal_body* bodies,
    current::current_batch_observation* observation) {
  const std::size_t slot = threadIdx.x;
  if (blockIdx.x != 0 || slot >= observation->count) { return; }
  const auto& body = bodies[slot];
  auto& output = observation->cases[slot];
  output.program_identity = body.program().identity;
  output.predecessor = body.program().predecessor;
  output.successor = body.standing().head();
  output.receiver_support = body.program().receiver_support;
  output.touched_support = exact::word{body.touched_support_value()};
  output.state = body.state();
  output.obstruction = body.obstruction();
  output.front_count = body.front_count();
  output.final_current_count = body.current_count();
  output.delta_count = body.delta_count();
  output.source_detached = true;
  output.compositional_quiescence = true;
  for (std::size_t index = 0; index < current::program_front_capacity; ++index) {
    output.fronts[index] = body.fronts()[index];
  }
  for (std::size_t index = 0; index < body.program().component_count; ++index) {
    output.components[index] = body.components()[index];
    output.compositional_quiescence &= output.components[index].certified;
  }
  for (std::size_t index = 0; index < body.current_count(); ++index) {
    output.final_currents[index] = body.current(index);
  }
  for (std::size_t index = 0; index < body.program().site_count; ++index) {
    output.morphology[index] = body.morphology_cells()[index];
  }
  for (std::size_t index = 0; index < body.delta_count(); ++index) {
    output.deltas[index] = body.deltas()[index];
  }
}

}  // namespace

cudaError_t launch_current_mount(const current::current_mount_batch* mount,
    current::resident_causal_body* bodies,
    current::current_batch_observation* observation) noexcept {
  mount_kernel<<<1, current::current_case_capacity>>>(mount, bodies, observation);
  return cudaGetLastError();
}

cudaError_t launch_current_advance(current::resident_causal_body* bodies,
    current::current_batch_observation* observation) noexcept {
  advance_kernel<<<current::current_case_capacity, current::sparse_current_capacity>>>(
      bodies, observation);
  return cudaGetLastError();
}

cudaError_t launch_current_observe(const current::resident_causal_body* bodies,
    current::current_batch_observation* observation) noexcept {
  observe_kernel<<<1, current::current_case_capacity>>>(bodies, observation);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
