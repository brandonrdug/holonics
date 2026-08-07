#pragma once

#include <cstddef>

#include <holonics/apparatus/phase_crystal_executor.hpp>
#include <holonics/apparatus/phase_crystal_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r18_verification_failures(
    const apparatus::phase_crystal_store_receipt& rest_load,
    const apparatus::phase_crystal_executor_receipt& execution,
    const event::phase_crystal_observation& actual,
    const event::phase_crystal_rest_record& handoff) noexcept;

}  // namespace holonics::tests
