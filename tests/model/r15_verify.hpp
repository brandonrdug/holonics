#pragma once

#include <cstddef>

#include <holonics/apparatus/return_conditioning_executor.hpp>
#include <holonics/apparatus/theorem_rest_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r15_verification_failures(
    const apparatus::theorem_rest_store_receipt& load,
    const apparatus::return_conditioning_mount& mount,
    const apparatus::return_conditioning_executor_receipt& execution,
    const event::return_conditioning_observation& actual,
    const event::theorem_production_rest_record& handoff,
    const event::dependent_theorem_setup& setup) noexcept;

}  // namespace holonics::tests
