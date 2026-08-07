#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/causal_current_executor.hpp>
#include <holonics/current/resident_causal_body.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_current_mount(
    const current::current_mount_batch* mount,
    current::resident_causal_body* bodies,
    current::current_batch_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_current_advance(
    current::resident_causal_body* bodies,
    current::current_batch_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_current_observe(
    const current::resident_causal_body* bodies,
    current::current_batch_observation* observation) noexcept;

}  // namespace holonics::apparatus
