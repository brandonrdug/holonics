#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/algebraic_variation_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_variation_mount(const algebraic_variation_mount* mount,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_variation_derive(const algebraic_variation_mount* mount,
    event::algebraic_variation_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_variation_form(const algebraic_variation_mount* mount,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_variation_resume(const event::checker_raw_return* returned,
    event::resident_algebraic_variation* production,
    event::algebraic_variation_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_variation_rest_remount(
    event::resident_algebraic_variation* production,
    event::algebraic_variation_rest_record* rest,
    event::algebraic_variation_rest_record* handoff,
    event::algebraic_variation_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_variation_observe(
    const event::algebraic_variation_observation* resident,
    event::algebraic_variation_observation* returned) noexcept;

}  // namespace holonics::apparatus
