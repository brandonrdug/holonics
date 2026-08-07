#pragma once

#include <cstddef>

#include <holonics/apparatus/causal_linear_executor.hpp>
#include <holonics/apparatus/causal_linear_probe.hpp>
#include <holonics/apparatus/causal_linear_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r25_verification_failures(bool sources_loaded,
    const apparatus::causal_linear_store_receipt& rest_load,
    const apparatus::causal_linear_executor_receipt& execution,
    const apparatus::causal_linear_probe_receipt& probe,
    const organ::causal_linear_receipt& changed,
    const event::causal_linear_observation& actual,
    const event::causal_linear_rest_record& handoff) noexcept;

}  // namespace holonics::tests
