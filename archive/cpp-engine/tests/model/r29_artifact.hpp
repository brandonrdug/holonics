#pragma once

#include <iosfwd>

#include <holonics/apparatus/arithmetic_spectral_executor.hpp>

namespace holonics::tests {

void write_r29_artifact(std::ostream& output, bool source_loaded,
    const apparatus::arithmetic_store_receipt& card,
    const apparatus::arithmetic_store_receipt& rest_load,
    const apparatus::arithmetic_store_receipt& rest_write,
    const apparatus::arithmetic_executor_receipt& execution,
    const event::arithmetic_spectral_observation& observation,
    const event::arithmetic_spectral_rest_record& handoff,
    std::size_t failures);

}  // namespace holonics::tests
