#pragma once

#include <cstddef>

#include <holonics/apparatus/arithmetic_spectral_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r29_verification_failures(bool source_loaded,
    const apparatus::arithmetic_store_receipt& rest_load,
    const apparatus::arithmetic_executor_receipt& execution,
    const event::arithmetic_spectral_observation& observation,
    const organ::arithmetic_spectral_workspace& workspace,
    const event::arithmetic_spectral_rest_record& handoff) noexcept;

}  // namespace holonics::tests
