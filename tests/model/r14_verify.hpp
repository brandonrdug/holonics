#pragma once

#include <cstddef>

#include <holonics/apparatus/theorem_production_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r14_verification_failures(
    const apparatus::theorem_production_executor_receipt& execution,
    const event::theorem_production_observation& actual,
    const event::theorem_production_rest_record& handoff) noexcept;

}  // namespace holonics::tests
