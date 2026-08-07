#pragma once

#include <cstddef>

#include <holonics/apparatus/boundary_condensation_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r8_verification_failures(
    const apparatus::boundary_condensation_executor_receipt& execution,
    const apparatus::boundary_condensation_observation& actual,
    const apparatus::boundary_condensation_observation& oracle) noexcept;

}  // namespace holonics::tests
