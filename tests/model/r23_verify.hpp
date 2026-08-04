#pragma once

#include <cstddef>

#include <holonics/apparatus/toric_cycle_executor.hpp>
#include <holonics/apparatus/toric_cycle_probe.hpp>
#include <holonics/apparatus/toric_cycle_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r23_verification_failures(
    const apparatus::toric_store_receipt& card_load,
    const apparatus::toric_store_receipt& rest_load,
    const apparatus::toric_executor_receipt& execution,
    const apparatus::toric_probe_receipt& probe,
    const organ::toric_cycle_receipt& changed,
    const event::toric_cycle_observation& actual,
    const event::toric_cycle_rest_record& handoff) noexcept;

}  // namespace holonics::tests
