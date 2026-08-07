#pragma once

#include <holonics/apparatus/toric_cycle_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::toric_cycle_mount r23_case(
    const event::cm_incidence_rest_record& inherited,
    const organ::toric_cycle_card& card) noexcept;
[[nodiscard]] organ::toric_cycle_card r23_host_card() noexcept;
[[nodiscard]] event::cm_incidence_rest_record r23_host_cm_rest() noexcept;

}  // namespace holonics::tests
