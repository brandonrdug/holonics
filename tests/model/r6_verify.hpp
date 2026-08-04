#pragma once

#include <cstddef>

#include <holonics/apparatus/weave_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r6_verification_failures(
    const current::weave_mount_batch& mount,
    const apparatus::weave_executor_receipt& execution,
    const apparatus::weave_batch_observation& actual,
    const apparatus::weave_batch_observation& oracle) noexcept;

}  // namespace holonics::tests
