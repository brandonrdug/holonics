#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/regular_singular_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_regular_singular_mount(
    const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_regular_singular_charts(
    const regular_singular_mount* mount,
    event::regular_singular_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_regular_singular_terms(
    const regular_singular_mount* mount,
    event::regular_singular_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_regular_singular_form(
    const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_regular_singular_resume(
    const event::checker_raw_return* returned,
    event::resident_regular_singular* production,
    event::regular_singular_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_regular_singular_rest_remount(
    const regular_singular_mount* mount,
    event::resident_regular_singular* production,
    event::regular_singular_rest_record* rest,
    event::regular_singular_rest_record* handoff,
    event::regular_singular_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_regular_singular_observe(
    const event::regular_singular_observation* resident,
    event::regular_singular_observation* returned) noexcept;

}  // namespace holonics::apparatus
