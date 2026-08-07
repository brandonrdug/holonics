#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/phase_crystal_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_phase_crystal_mount(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_phase_crystal_cases(const phase_crystal_mount* mount,
    event::phase_crystal_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_phase_crystal_form(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_phase_crystal_resume(const event::checker_raw_return* returned,
    event::resident_phase_crystal* production,
    event::phase_crystal_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_phase_crystal_rest_remount(const phase_crystal_mount* mount,
    event::resident_phase_crystal* production,
    event::phase_crystal_rest_record* rest,
    event::phase_crystal_rest_record* handoff,
    event::phase_crystal_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_phase_crystal_observe(
    const event::phase_crystal_observation* resident,
    event::phase_crystal_observation* returned) noexcept;

}  // namespace holonics::apparatus
