#pragma once

#include <cstddef>

#include <holonics/apparatus/generative_math_executor.hpp>

#include "r12_oracle.hpp"

namespace holonics::tests {

[[nodiscard]] bool same_generated_bytes(
    const char* actual, std::size_t actual_count, const char* expected) noexcept;
[[nodiscard]] std::size_t r12_verification_failures(
    const apparatus::generative_math_executor_receipt& execution,
    const apparatus::generative_math_observation& actual,
    const r12_expected& expected) noexcept;

}  // namespace holonics::tests
