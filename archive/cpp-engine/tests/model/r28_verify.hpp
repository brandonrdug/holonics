#pragma once

#include <cstddef>

#include <holonics/apparatus/hodge_realization_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r28_verification_failures(bool source_loaded,
    const apparatus::hodge_store_receipt& rest_load,
    const apparatus::hodge_executor_receipt& execution,
    const event::hodge_realization_observation& actual,
    const event::hodge_realization_rest_record& handoff) noexcept;

}  // namespace holonics::tests
