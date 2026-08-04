#pragma once

#include <cstddef>

#include <holonics/apparatus/lean_checker_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r13_verification_failures(
    const apparatus::lean_checker_executor_receipt& execution,
    const event::checker_observation& actual) noexcept;

}  // namespace holonics::tests
