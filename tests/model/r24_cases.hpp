#pragma once

#include <holonics/apparatus/algebraic_variation_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::algebraic_variation_mount r24_case(
    const event::toric_cycle_rest_record& inherited,
    const organ::algebraic_variation_card& card) noexcept;
[[nodiscard]] organ::algebraic_variation_card r24_host_card() noexcept;
[[nodiscard]] event::toric_cycle_rest_record r24_host_toric_rest() noexcept;

}  // namespace holonics::tests
