#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/receiver_geometry_executor.hpp>
#include <holonics/current/resident_weave.hpp>
#include <holonics/receiver/resident_geometry.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_receiver_geometry_mount(
    const receiver_geometry_mount* mount,
    current::resident_weave* current,
    receiver::resident_geometry* receiver) noexcept;

[[nodiscard]] cudaError_t launch_receiver_geometry_advance(
    current::resident_weave* current,
    receiver::resident_geometry* receiver) noexcept;

[[nodiscard]] cudaError_t launch_receiver_geometry_observe(
    const current::resident_weave* current,
    const receiver::resident_geometry* receiver,
    receiver_geometry_observation* observation) noexcept;

}  // namespace holonics::apparatus
