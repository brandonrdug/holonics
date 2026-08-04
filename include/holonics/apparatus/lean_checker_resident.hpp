#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/lean_checker_executor.hpp>
#include <holonics/event/resident_checker_current.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_lean_checker_stage(
    const lean_checker_mount* mount,
    event::resident_checker_current* current,
    event::checker_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_lean_checker_resume(
    const event::checker_raw_return* returned,
    event::resident_checker_current* current,
    event::checker_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_lean_checker_observe(
    const event::checker_observation* resident,
    event::checker_observation* returned) noexcept;

}  // namespace holonics::apparatus
