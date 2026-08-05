#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/arithmetic_spectral_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_arithmetic_mount(const arithmetic_spectral_mount* mount,
    event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_fields(event::arithmetic_spectral_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_curves(event::arithmetic_spectral_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_fixed(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_candidates(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_compose(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_points(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_currents(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_close(event::arithmetic_spectral_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_form(event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_resume(const event::checker_raw_return* raw,
    event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_rest(event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_rest_record* rest, event::arithmetic_spectral_rest_record* handoff,
    event::arithmetic_spectral_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_arithmetic_observe(
    const event::arithmetic_spectral_observation* resident,
    event::arithmetic_spectral_observation* returned) noexcept;

}  // namespace holonics::apparatus
