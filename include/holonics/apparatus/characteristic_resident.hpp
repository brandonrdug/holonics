#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/characteristic_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_characteristic_mount(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_cases(const characteristic_mount* mount,
    event::characteristic_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_form(const characteristic_mount* mount,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_resume(const event::checker_raw_return* returned,
    event::resident_characteristic* production,
    event::characteristic_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_rest_remount(
    const characteristic_mount* mount, event::resident_characteristic* production,
    event::characteristic_rest_record* rest,
    event::characteristic_rest_record* handoff,
    event::characteristic_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_characteristic_observe(
    const event::characteristic_observation* resident,
    event::characteristic_observation* returned) noexcept;

}  // namespace holonics::apparatus
