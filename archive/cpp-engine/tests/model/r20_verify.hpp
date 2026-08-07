#pragma once

#include <cstddef>

#include <holonics/apparatus/regular_singular_store_adapter.hpp>
#include "r20_cases.hpp"

namespace holonics::tests {

[[nodiscard]] std::size_t r20_verification_failures(
    const apparatus::regular_singular_store_receipt& rest_load,
    const apparatus::regular_singular_executor_receipt& execution,
    const event::regular_singular_observation& actual,
    const event::regular_singular_rest_record& handoff) noexcept;

}  // namespace holonics::tests
