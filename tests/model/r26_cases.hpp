#pragma once

#include <holonics/apparatus/intrinsic_hypergeometry_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::intrinsic_hypergeometry_mount r26_case(
    const event::causal_linear_rest_record& inherited,
    const organ::intrinsic_hypergeometry_card& card,
    const organ::cm_problem_card& cm,
    const organ::algebraic_variation_card& variation) noexcept;
[[nodiscard]] organ::intrinsic_hypergeometry_card r26_host_card() noexcept;

}  // namespace holonics::tests
