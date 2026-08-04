#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/weave_executor.hpp>
#include <holonics/current/resident_weave.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_weave_mount(
    const current::weave_mount_batch* mount,
    current::resident_weave* bodies,
    weave_batch_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_weave_advance(
    current::resident_weave* bodies,
    const weave_batch_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_weave_observe(
    const current::resident_weave* bodies,
    weave_batch_observation* observation) noexcept;

}  // namespace holonics::apparatus
