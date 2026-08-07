#pragma once

#include <iosfwd>

#include "r23_verify.hpp"

namespace holonics::tests {

void write_r23_artifact(std::ostream& output,
    const apparatus::toric_store_receipt& card_load,
    const apparatus::toric_store_receipt& rest_load,
    const apparatus::toric_store_receipt& rest_write,
    const apparatus::toric_executor_receipt& execution,
    const apparatus::toric_probe_receipt& probe,
    const organ::toric_cycle_receipt& changed,
    const event::toric_cycle_observation& value,
    const event::toric_cycle_rest_record& handoff,
    std::size_t failures) noexcept;
void write_r23_atlas(std::ostream& output,
    const organ::toric_cycle_receipt& value) noexcept;

}  // namespace holonics::tests
