#pragma once

#include <cuda_runtime_api.h>

#include <holonics/apparatus/expression_geometry_executor.hpp>

namespace holonics::apparatus {

[[nodiscard]] cudaError_t launch_expression_geometry_mount(
    const expression_geometry_mount* mount, event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_sources(
    const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_changed(
    const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_compose(
    const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_changed_close(
    const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_form(
    event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_resume(const event::checker_raw_return* raw,
    event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_rest(
    event::resident_expression_geometry* production,
    event::expression_geometry_rest_record* rest,
    event::expression_geometry_rest_record* handoff,
    event::expression_geometry_observation* observation) noexcept;
[[nodiscard]] cudaError_t launch_expression_geometry_observe(
    const event::expression_geometry_observation* resident,
    event::expression_geometry_observation* returned) noexcept;

}  // namespace holonics::apparatus
