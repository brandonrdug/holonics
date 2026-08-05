#pragma once

#include <holonics/apparatus/expression_geometry_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::expression_geometry_mount r27_case(
    const event::intrinsic_hypergeometry_rest_record& inherited,
    const organ::expression_geometry_card& card) noexcept;
[[nodiscard]] organ::expression_geometry_card r27_host_card() noexcept;

}  // namespace holonics::tests
