#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/intrinsic_hypergeometry_executor.hpp>
#include <holonics/event/resident_intrinsic_hypergeometry_mount.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_intrinsic_hypergeometry_mount(
    const intrinsic_hypergeometry_mount* mount,
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_phase_sources(
    const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_nonphase_sources(
    const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_phase_transport(
    const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_changed_source(
    const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_changed_transport(
    const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_aggregate(
    const intrinsic_hypergeometry_mount* mount,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_form(
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_resume(const event::checker_raw_return* returned,
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_rest_remount(
    event::resident_intrinsic_hypergeometry* production,
    event::intrinsic_hypergeometry_rest_record* rest,
    event::intrinsic_hypergeometry_rest_record* handoff,
    event::intrinsic_hypergeometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_intrinsic_observe(
    const event::intrinsic_hypergeometry_observation* resident,
    event::intrinsic_hypergeometry_observation* returned) noexcept;

}  // namespace holonics::apparatus
