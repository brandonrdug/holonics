#pragma once

#include <iosfwd>

#include "r28_verify.hpp"

namespace holonics::tests {

void write_r28_artifact(std::ostream& out, bool source_loaded,
    const apparatus::hodge_store_receipt& source_load,
    const apparatus::hodge_store_receipt& rest_load,
    const apparatus::hodge_store_receipt& rest_write,
    const apparatus::hodge_executor_receipt& execution,
    const event::hodge_realization_observation& observation,
    const event::hodge_realization_rest_record& handoff, std::size_t failures);

}  // namespace holonics::tests
