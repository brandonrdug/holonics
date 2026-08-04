#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/body_lifecycle_executor.hpp>
#include <holonics/event/lifecycle_law.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_body_open(
    const body_lifecycle_input* input,
    body::continuing_body* standing,
    event::live_pending* pending,
    event::lifecycle_output* output) noexcept;

[[nodiscard]] cudaError_t launch_body_resume_rest(
    const event::deed_return* returned,
    body::continuing_body* standing,
    event::live_pending* pending,
    event::live_delta* delta,
    body::rest_record* rest,
    event::lifecycle_output* output) noexcept;

[[nodiscard]] cudaError_t launch_body_remount(
    const body::rest_record* rest,
    body::continuing_body* standing,
    event::lifecycle_output* output) noexcept;

[[nodiscard]] cudaError_t launch_body_adversarial(
    event::lifecycle_output* output) noexcept;

}  // namespace holonics::apparatus
