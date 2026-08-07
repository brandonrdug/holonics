#pragma once

#include <cstddef>

#include <holonics/apparatus/characteristic_executor.hpp>
#include <holonics/apparatus/characteristic_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r19_verification_failures(
    const apparatus::characteristic_store_receipt& rest_load,
    const apparatus::characteristic_executor_receipt& execution,
    const event::characteristic_observation& actual,
    const event::characteristic_rest_record& handoff) noexcept;

}  // namespace holonics::tests
