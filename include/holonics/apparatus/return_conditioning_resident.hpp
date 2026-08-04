#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/return_conditioning_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_return_conditioning_mount(
    const return_conditioning_mount* mount,
    event::resident_theorem_production* production,
    event::return_conditioning_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_return_conditioning_ablation(
    const return_conditioning_mount* mount,
    event::theorem_production_rest_record* projected,
    event::resident_theorem_production* ablation,
    event::dependent_theorem_setup* setup,
    event::return_conditioning_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_return_conditioning_rest(
    event::resident_theorem_production* production,
    event::theorem_production_rest_record* handoff,
    event::return_conditioning_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_return_conditioning_observe(
    const event::return_conditioning_observation* resident,
    event::return_conditioning_observation* returned) noexcept;

}  // namespace holonics::apparatus
