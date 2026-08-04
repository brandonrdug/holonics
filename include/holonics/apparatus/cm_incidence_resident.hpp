#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/cm_incidence_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_cm_mount(const cm_incidence_mount* mount,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_translations(
    const cm_incidence_mount* mount, event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_periodic(
    event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_window(
    event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_characteristics(
    const cm_incidence_mount* mount, event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_form(const cm_incidence_mount* mount,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_resume(const event::checker_raw_return* returned,
    event::resident_cm_incidence* production,
    event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_rest_remount(event::resident_cm_incidence* production,
    event::cm_incidence_rest_record* rest, event::cm_incidence_rest_record* handoff,
    event::cm_incidence_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_cm_observe(
    const event::cm_incidence_observation* resident,
    event::cm_incidence_observation* returned) noexcept;

}  // namespace holonics::apparatus
