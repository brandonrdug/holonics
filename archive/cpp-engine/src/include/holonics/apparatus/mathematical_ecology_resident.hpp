#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/mathematical_ecology_executor.hpp>
#include <holonics/event/resident_mathematical_ecology.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_mathematical_ecology_mount(
    const mathematical_ecology_mount* mount,
    event::resident_mathematical_ecology* canonical,
    event::resident_mathematical_ecology* reordered,
    mathematical_ecology_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_mathematical_ecology_reconstruction(
    const mathematical_ecology_mount* mount,
    const event::resident_mathematical_ecology* canonical,
    const event::resident_mathematical_ecology* reordered,
    mathematical_ecology_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_mathematical_ecology_observe(
    const mathematical_ecology_observation* resident,
    mathematical_ecology_observation* returned) noexcept;

}  // namespace holonics::apparatus
