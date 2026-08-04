#pragma once

#include <holonics/apparatus/cm_incidence_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::cm_incidence_mount r22_case(
    const event::blind_reconstruction_rest_record& inherited,
    const organ::cm_problem_card& card) noexcept;
[[nodiscard]] organ::cm_problem_card r22_host_card() noexcept;
[[nodiscard]] event::blind_reconstruction_rest_record r22_host_blind_rest() noexcept;

}  // namespace holonics::tests
