#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/toric_cycle_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_toric_mount(const toric_cycle_mount* mount,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_toric_derive(const toric_cycle_mount* mount,
    event::toric_cycle_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_toric_form(const toric_cycle_mount* mount,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_toric_resume(const event::checker_raw_return* returned,
    event::resident_toric_cycle* production,
    event::toric_cycle_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_toric_rest_remount(
    event::resident_toric_cycle* production, event::toric_cycle_rest_record* rest,
    event::toric_cycle_rest_record* handoff,
    event::toric_cycle_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_toric_observe(
    const event::toric_cycle_observation* resident,
    event::toric_cycle_observation* returned) noexcept;

}  // namespace holonics::apparatus
