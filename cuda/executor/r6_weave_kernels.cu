#include <cstddef>
#include <cstdint>
#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/weave_resident.hpp>

#include "r6_weave_law.cuh"

namespace holonics::apparatus {
namespace {

__global__ void mount_kernel(const current::weave_mount_batch* mount,
    current::resident_weave* bodies,
    weave_batch_observation* observation) {
  if (blockIdx.x != 0) { return; }
  if (threadIdx.x == 0) { observation->count = mount->count; }
  const std::size_t slot = threadIdx.x;
  if (slot >= mount->count || slot >= current::weave_case_capacity) { return; }
  ::new (static_cast<void*>(bodies + slot)) current::resident_weave{mount->programs[slot]};
  const auto validation = current::validate_weave_program(mount->programs[slot]);
  if (validation != current::weave_obstruction::none) { bodies[slot].set_validation(validation); }
}

__global__ void advance_kernel(current::resident_weave* bodies,
    const weave_batch_observation* observation) {
  const std::size_t case_slot = blockIdx.x;
  if (case_slot >= observation->count) { return; }
  auto& body = bodies[case_slot];
  if (body.validation() != current::weave_obstruction::none) { return; }
  __shared__ bool committed;
  for (std::uint16_t layer = 0; layer < body.program().layer_count; ++layer) {
    r6_device::apply_layer(body, layer, committed);
    if (!committed) { return; }
  }
  if (threadIdx.x == 0) {
    body.begin_resource_return();
    committed = body.commit_resource_return();
  }
  __syncthreads();
  if (!committed) { return; }
  if (threadIdx.x < body.program().cell_count) { body.apply_resource_cell(threadIdx.x); }
}

__global__ void observe_kernel(const current::resident_weave* bodies,
    weave_batch_observation* observation) {
  const std::size_t case_slot = blockIdx.x;
  if (case_slot >= observation->count) { return; }
  const auto& body = bodies[case_slot];
  const auto& program = body.program();
  auto& output = observation->cases[case_slot];
  if (threadIdx.x < current::weave_variant_capacity) {
    auto& variant = output.variants[threadIdx.x];
    variant.partition_count = program.variant_partitions[threadIdx.x];
    variant.completion_order = static_cast<std::uint16_t>(threadIdx.x);
    variant.successor = current::apply_selected_events(program,
        program.variant_orders[threadIdx.x], program.event_count, program.layer_count);
    variant.successor = r6_device::apply_resource_snapshot(program, variant.successor);
    variant.non_resumable = true;
  }
  __syncthreads();
  if (threadIdx.x != 0) { return; }
  auto& semantic = output.semantic;
  semantic.program_identity = program.identity;
  semantic.predecessor = current::predecessor_snapshot(program);
  semantic.successor = body.standing();
  semantic.delta_count = program.event_count;
  semantic.committed_layers = body.committed_layers();
  for (std::size_t slot = 0; slot < program.event_count; ++slot) {
    semantic.deltas[slot] = body.delta(slot);
  }
  semantic.serial = current::make_serial_gluing(program, 0, 1);
  semantic.parallel = current::make_interchange(program, 2, 3);
  semantic.coherence = current::make_higher_coherence(program, 4, 5, 6);
  semantic.interaction = current::make_interaction(program);
  semantic.recurrence = current::make_recurrence(program);
  semantic.unproved_overlap = current::make_unproved_overlap(program);
  semantic.resource = body.resource();
  semantic.canonical_commit =
      current::equal_complete_standing(semantic.successor, output.variants[0].successor);
  output.partition_successors_equal = true;
  output.completion_successors_equal = true;
  for (std::size_t variant = 1; variant < current::weave_variant_capacity; ++variant) {
    const bool equal = current::equal_complete_standing(
        output.variants[0].successor, output.variants[variant].successor);
    output.partition_successors_equal &= equal;
    output.completion_successors_equal &= equal;
  }
}

}  // namespace

cudaError_t launch_weave_mount(const current::weave_mount_batch* mount,
    current::resident_weave* bodies,
    weave_batch_observation* observation) noexcept {
  mount_kernel<<<1, current::weave_case_capacity>>>(mount, bodies, observation);
  return cudaGetLastError();
}

cudaError_t launch_weave_advance(current::resident_weave* bodies,
    const weave_batch_observation* observation) noexcept {
  advance_kernel<<<current::weave_case_capacity, current::weave_cell_capacity>>>(
      bodies, observation);
  return cudaGetLastError();
}

cudaError_t launch_weave_observe(const current::resident_weave* bodies,
    weave_batch_observation* observation) noexcept {
  observe_kernel<<<current::weave_case_capacity, current::weave_cell_capacity>>>(
      bodies, observation);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
