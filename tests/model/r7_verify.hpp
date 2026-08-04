#pragma once

#include <cstddef>

#include <holonics/apparatus/receiver_geometry_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r7_verification_failures(
    const apparatus::receiver_geometry_executor_receipt& execution,
    const apparatus::receiver_geometry_observation& actual,
    const apparatus::receiver_geometry_observation& oracle) noexcept;

}  // namespace holonics::tests
