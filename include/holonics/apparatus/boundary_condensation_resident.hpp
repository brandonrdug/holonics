#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/boundary_condensation_executor.hpp>
#include <holonics/event/resident_condensation.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_boundary_condensation_mount(
    const boundary_condensation_mount* mount,
    event::resident_condensation* body) noexcept;

[[nodiscard]] cudaError_t launch_boundary_condensation_advance(
    event::resident_condensation* body) noexcept;

[[nodiscard]] cudaError_t launch_boundary_condensation_observe(
    const event::resident_condensation* body,
    boundary_condensation_observation* observation) noexcept;

}  // namespace holonics::apparatus
