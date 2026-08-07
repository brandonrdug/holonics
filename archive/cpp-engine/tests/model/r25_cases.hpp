#pragma once

#include <holonics/apparatus/causal_linear_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::causal_linear_mount r25_case(
    const event::algebraic_variation_rest_record& inherited,
    const organ::causal_linear_card& card, const organ::cm_problem_card& cm,
    const organ::toric_cycle_card& toric,
    const organ::algebraic_variation_card& variation) noexcept;
[[nodiscard]] organ::causal_linear_card r25_host_card() noexcept;

}  // namespace holonics::tests
