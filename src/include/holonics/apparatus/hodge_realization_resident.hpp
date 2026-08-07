#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/hodge_realization_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_hodge_mount(const hodge_realization_mount* mount,
    event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_factors(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_product(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_translations(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_cycles(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_blowups(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_close(event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_form(event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_resume(const event::checker_raw_return* raw,
    event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_rest(event::resident_hodge_realization* production,
    event::hodge_realization_rest_record* rest, event::hodge_realization_rest_record* handoff,
    event::hodge_realization_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_hodge_observe(const event::hodge_realization_observation* resident,
    event::hodge_realization_observation* returned) noexcept;

}  // namespace holonics::apparatus
