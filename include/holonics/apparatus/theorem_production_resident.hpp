#pragma once

#include <cuda_runtime.h>

#include <holonics/apparatus/theorem_production_executor.hpp>
#include <holonics/event/resident_theorem_production.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_theorem_production_stage(
    const theorem_production_mount* mount,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_theorem_production_resume(
    const event::checker_raw_return* returned,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_theorem_production_rest(
    event::resident_theorem_production* production,
    event::theorem_production_rest_record* rest,
    event::theorem_production_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_theorem_production_remount_probe(
    const theorem_production_mount* mount,
    const event::theorem_production_rest_record* rest,
    event::theorem_production_rest_record* handoff,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) noexcept;

[[nodiscard]] cudaError_t launch_theorem_production_observe(
    const event::theorem_production_observation* resident,
    event::theorem_production_observation* returned) noexcept;

}  // namespace holonics::apparatus
