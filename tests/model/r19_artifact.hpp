#pragma once

#include <iosfwd>

#include "r19_verify.hpp"

namespace holonics::tests {

void write_r19_atlas(std::ostream& output,
    const organ::characteristic_receipt& value) noexcept;
void write_r19_artifact(std::ostream& output,
    const apparatus::characteristic_store_receipt& rest_load,
    const apparatus::characteristic_store_receipt& rest_write,
    const apparatus::characteristic_executor_receipt& execution,
    const event::characteristic_observation& value,
    const event::characteristic_rest_record& handoff,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
