#pragma once

#include <cstddef>

#include <holonics/apparatus/conditioning_executor.hpp>

#include "r10_oracle.hpp"

namespace holonics::tests {
[[nodiscard]] std::size_t r10_verification_failures(
    const apparatus::conditioning_executor_receipt& execution,
    const apparatus::conditioning_observation& actual,
    const r10_expected& expected) noexcept;
}  // namespace holonics::tests
