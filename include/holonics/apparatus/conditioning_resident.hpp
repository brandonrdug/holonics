#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/conditioning_executor.hpp>
#include <holonics/event/resident_conditioned_organ.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_conditioning_mount(
    const conditioning_foundation* foundation,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_conditioning_train(
    const conditioning_passage* passage,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_conditioning_rest(
    event::resident_conditioned_organ* production,
    event::conditioned_organ_rest_record* rest,
    conditioning_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_conditioning_remount(
    const event::conditioned_organ_rest_record* rest,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_conditioning_ablation(
    const conditioning_foundation* foundation,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* ablation,
    conditioning_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_conditioning_observe(
    const conditioning_observation* resident,
    conditioning_observation* returned) noexcept;

}  // namespace holonics::apparatus
