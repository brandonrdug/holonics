#pragma once

#include <holonics/apparatus/hodge_realization_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::hodge_realization_mount r28_case(
    const event::expression_geometry_rest_record& inherited,
    const organ::hodge_realization_card& card) noexcept;
[[nodiscard]] organ::hodge_realization_card r28_host_card() noexcept;

}  // namespace holonics::tests
