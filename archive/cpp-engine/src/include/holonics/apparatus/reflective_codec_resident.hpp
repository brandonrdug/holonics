#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/reflective_codec_executor.hpp>
#include <holonics/event/resident_reflective_codec.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_reflective_codec_mount(
    const reflective_codec_mount* mount,
    event::resident_reflective_codec* body,
    reflective_codec_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_reflective_codec_revise_rest(
    const reflective_codec_deed* deed,
    event::resident_reflective_codec* body,
    event::reflective_codec_rest_record* rest,
    reflective_codec_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_reflective_codec_remount(
    const reflective_codec_deed* deed,
    const event::reflective_codec_rest_record* rest,
    event::resident_reflective_codec* body,
    reflective_codec_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_reflective_codec_observe(
    const reflective_codec_observation* resident,
    reflective_codec_observation* returned) noexcept;

}  // namespace holonics::apparatus
