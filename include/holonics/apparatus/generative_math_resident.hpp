#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/generative_math_executor.hpp>
#include <holonics/event/resident_generative_math_current.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_generative_math_mount(
    const generative_math_mount* mount,
    event::resident_generative_math_current* current,
    generative_math_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_generative_math_form(
    const generative_math_mount* mount,
    event::resident_generative_math_current* current,
    generative_math_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_generative_math_observe(
    const generative_math_observation* resident,
    generative_math_observation* returned) noexcept;

}  // namespace holonics::apparatus
