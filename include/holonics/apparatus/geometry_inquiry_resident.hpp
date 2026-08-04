#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/geometry_inquiry_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_geometry_inquiry_mount(
    const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_geometry_inquiry_probes(
    const geometry_inquiry_mount* mount,
    event::geometry_inquiry_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_geometry_inquiry_form(
    const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_geometry_inquiry_resume(
    const event::checker_raw_return* returned,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_geometry_inquiry_rest_remount(
    const geometry_inquiry_mount* mount,
    event::resident_geometry_inquiry* production,
    event::geometry_inquiry_rest_record* rest,
    event::geometry_inquiry_rest_record* handoff,
    event::geometry_inquiry_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_geometry_inquiry_observe(
    const event::geometry_inquiry_observation* resident,
    event::geometry_inquiry_observation* returned) noexcept;

}  // namespace holonics::apparatus
