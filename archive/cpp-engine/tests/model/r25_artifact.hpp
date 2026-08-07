#pragma once

#include <iosfwd>

#include "r25_verify.hpp"

namespace holonics::tests {

void write_r25_artifact(std::ostream& output, bool sources_loaded,
    const apparatus::causal_linear_store_receipt& card_load,
    const apparatus::causal_linear_store_receipt& rest_load,
    const apparatus::causal_linear_store_receipt& rest_write,
    const apparatus::causal_linear_executor_receipt& execution,
    const apparatus::causal_linear_probe_receipt& probe,
    const organ::causal_linear_receipt& changed,
    const event::causal_linear_observation& value,
    const event::causal_linear_rest_record& handoff,
    std::size_t failures) noexcept;
void write_r25_atlas(std::ostream& output,
    const organ::causal_linear_receipt& value) noexcept;

}  // namespace holonics::tests
