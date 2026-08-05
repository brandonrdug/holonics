#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/causal_linear_executor.hpp>
#include <holonics/event/resident_causal_linear_mount.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_causal_linear_mount(const causal_linear_mount* mount,
    event::resident_causal_linear* production,
    event::causal_linear_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_causal_linear_sources(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_causal_linear_controls(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_causal_linear_aggregate(const causal_linear_mount* mount,
    event::causal_linear_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_causal_linear_form(
    event::resident_causal_linear* production,
    event::causal_linear_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_causal_linear_resume(const event::checker_raw_return* returned,
    event::resident_causal_linear* production,
    event::causal_linear_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_causal_linear_rest_remount(
    event::resident_causal_linear* production, event::causal_linear_rest_record* rest,
    event::causal_linear_rest_record* handoff,
    event::causal_linear_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_causal_linear_observe(
    const event::causal_linear_observation* resident,
    event::causal_linear_observation* returned) noexcept;

}  // namespace holonics::apparatus
