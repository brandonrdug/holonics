#pragma once

#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/weave_resident.hpp>

namespace holonics::apparatus::r6_device {

__device__ inline bool interaction_layer(
    const current::weave_program& program,
    std::size_t offset,
    std::size_t count) noexcept {
  return program.interaction_left >= offset && program.interaction_left < offset + count &&
      program.interaction_right >= offset && program.interaction_right < offset + count;
}

__device__ inline void apply_layer(
    current::resident_weave& body,
    std::uint16_t layer,
    bool& committed) noexcept {
  const auto& program = body.program();
  const std::size_t offset = program.layer_offsets[layer];
  const std::size_t count = program.layer_counts[layer];
  if (threadIdx.x == 0) {
    std::uint64_t logical = 0;
    for (std::size_t member = 0; member < count; ++member) {
      body.stage(offset + member);
      logical += program.events[offset + member].logical_resource.value();
    }
    committed = body.commit_layer(logical, program.identity.value() + layer);
  }
  __syncthreads();
  if (!committed) { return; }
  if (interaction_layer(program, offset, count)) {
    if (threadIdx.x == 0) {
      body.apply_cell(program.interaction_left);
      body.apply_cell(program.interaction_right);
      body.equalize_interaction();
    }
  } else if (threadIdx.x < count) {
    body.apply_cell(offset + threadIdx.x);
  }
  __syncthreads();
}

__device__ inline current::weave_snapshot apply_resource_snapshot(
    const current::weave_program& program,
    current::weave_snapshot standing) noexcept {
  const bool pressure =
      program.returned_resource.available_bytes.value() < program.resource.required_bytes.value() ||
      program.returned_resource.resident_bytes.value() >
          program.returned_resource.available_bytes.value() ||
      program.returned_resource.temperature_upper_millikelvin.value() >
          program.resource.temperature_limit_millikelvin.value();
  if (!pressure) { return standing; }
  standing.head = exact::word{standing.head.value() + 1U};
  if (!program.resource.alternative_declared) {
    standing.obstruction = current::weave_obstruction::returned_resource_open;
    return standing;
  }
  for (std::size_t cell = 0; cell < standing.cell_count; ++cell) {
    standing.cells[cell].placement = program.resource.alternative_partition;
    standing.cells[cell].aperture = program.resource.alternative_aperture;
  }
  return standing;
}

}  // namespace holonics::apparatus::r6_device
