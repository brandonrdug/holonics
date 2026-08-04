#pragma once

#include <cstddef>

#include <holonics/apparatus/cm_incidence_executor.hpp>
#include <holonics/apparatus/cm_incidence_probe.hpp>
#include <holonics/apparatus/cm_incidence_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r22_verification_failures(
    const apparatus::cm_store_receipt& card_load,
    const apparatus::cm_store_receipt& rest_load,
    const apparatus::cm_executor_receipt& execution,
    const apparatus::cm_probe_receipt& probe,
    const organ::cm_incidence_receipt& changed,
    const event::cm_incidence_observation& actual,
    const event::cm_incidence_rest_record& handoff) noexcept;

}  // namespace holonics::tests
