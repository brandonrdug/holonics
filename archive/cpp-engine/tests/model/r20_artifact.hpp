#pragma once

#include <iosfwd>

#include "r20_verify.hpp"

namespace holonics::tests {

void write_r20_atlas(std::ostream& output,
    const organ::regular_singular_receipt& value) noexcept;
void write_r20_artifact(std::ostream& output,
    const apparatus::regular_singular_store_receipt& rest_load,
    const apparatus::regular_singular_store_receipt& rest_write,
    const apparatus::regular_singular_executor_receipt& execution,
    const event::regular_singular_observation& value,
    const event::regular_singular_rest_record& handoff,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
