#pragma once

#include <cstddef>

#include <holonics/apparatus/causal_current_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r5_verification_failures(
    const current::current_mount_batch& mount,
    const apparatus::causal_current_executor_receipt& execution,
    const current::current_batch_observation& actual,
    const current::current_batch_observation& oracle,
    const apparatus::causal_current_executor_receipt& unavailable) noexcept;

}  // namespace holonics::tests
