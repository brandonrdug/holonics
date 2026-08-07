#pragma once

#include <cstddef>

#include <holonics/apparatus/body_lifecycle_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::body_lifecycle_input r4_input() noexcept;

[[nodiscard]] std::size_t r4_verification_failures(
    const apparatus::body_lifecycle_input& input,
    const apparatus::body_lifecycle_executor_receipt& execution,
    const event::lifecycle_output& output) noexcept;

}  // namespace holonics::tests
