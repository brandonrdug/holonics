#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/blind_reconstruction_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_blind_mount(const blind_reconstruction_mount* mount,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_code(
    const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_pairs(
    const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_moments(
    const blind_reconstruction_mount* mount,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_form_code(
    const blind_reconstruction_mount* mount,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_resume_code(const event::checker_raw_return* returned,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_form_moment(
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_resume_moment(const event::checker_raw_return* returned,
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_rest_remount(
    event::resident_blind_reconstruction* production,
    event::blind_reconstruction_rest_record* rest,
    event::blind_reconstruction_rest_record* handoff,
    event::blind_reconstruction_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_blind_observe(
    const event::blind_reconstruction_observation* resident,
    event::blind_reconstruction_observation* returned) noexcept;

}  // namespace holonics::apparatus
