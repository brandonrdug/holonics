#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/terminal_theorem_executor.hpp>
#include <holonics/event/resident_dependent_theorem_production.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_terminal_theorem_stage(
    const terminal_theorem_mount* mount,
    event::theorem_production_rest_record* projected,
    event::resident_dependent_theorem_production* production,
    event::resident_dependent_theorem_production* ablation,
    event::terminal_theorem_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_terminal_theorem_resume(
    const event::checker_raw_return* returned,
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_terminal_theorem_rest(
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_rest_record* rest,
    event::terminal_theorem_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_terminal_theorem_remount(
    const terminal_theorem_mount* mount,
    const event::terminal_theorem_rest_record* rest,
    event::terminal_theorem_rest_record* handoff,
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_terminal_theorem_observe(
    const event::terminal_theorem_observation* resident,
    event::terminal_theorem_observation* returned) noexcept;

}  // namespace holonics::apparatus
