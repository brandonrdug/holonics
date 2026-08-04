#pragma once

#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/receiver_geometry_resident.hpp>

#include "r6_weave_law.cuh"

namespace holonics::apparatus::r7_device {

__device__ inline exact::word returned_stress(
    const current::weave_program& program) noexcept {
  std::uint64_t result = 0;
  for (std::size_t slot = 0; slot < program.event_count; ++slot) {
    result += program.events[slot].stress.value();
  }
  return exact::word{result};
}

__device__ inline void apply_geometry(
    const current::resident_weave& body,
    receiver::resident_geometry& geometry) noexcept {
  const auto& program = geometry.program();
  auto& output = geometry.observation();
  if (threadIdx.x == 0) { output.swing = receiver::projective_swing(program.swing); }
  if (threadIdx.x == 1) { output.sameness = receiver::distinguish_sameness(program.sameness); }
  if (threadIdx.x == 2) { output.projection = receiver::project_shadow(program.projection); }
  if (threadIdx.x == 3) { output.connection = receiver::carry_connection(program.connection); }
  if (threadIdx.x == 4) {
    output.hypergeometric = receiver::carry_gauss_solution(program.hypergeometric);
  }
  if (threadIdx.x == 5) {
    const bool interchange =
        current::make_interchange(body.program(), 2, 3).complete_successor_equal;
    output.carrier = receiver::weave_extended_carriers(program.carrier, interchange);
  }
  if (threadIdx.x == 6) {
    const auto recurrence = current::make_recurrence(body.program());
    output.information = receiver::receive_information_geometry(program.information,
        body.standing().head, body.standing().cells[7].current,
        returned_stress(body.program()), recurrence.complete_state_recurrence);
  }
  __syncthreads();
  if (threadIdx.x == 0) {
    output.all_deeds_returned = output.swing.projectively_equal &&
        output.sameness.digest_collision_retained &&
        output.projection.unresolved_preimage && output.connection.curvature_certified &&
        output.hypergeometric.recurrence_exact &&
        output.carrier.higher_boundary_squared_zero &&
        output.information.causal_accessible;
  }
}

}  // namespace holonics::apparatus::r7_device
