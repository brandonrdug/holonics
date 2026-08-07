#pragma once

#include <iosfwd>

#include "r22_verify.hpp"

namespace holonics::tests {

void write_r22_artifact(std::ostream& output,
    const apparatus::cm_store_receipt& card_load,
    const apparatus::cm_store_receipt& rest_load,
    const apparatus::cm_store_receipt& rest_write,
    const apparatus::cm_executor_receipt& execution,
    const apparatus::cm_probe_receipt& probe,
    const organ::cm_incidence_receipt& changed,
    const event::cm_incidence_observation& value,
    const event::cm_incidence_rest_record& handoff,
    std::size_t failures) noexcept;
void write_r22_atlas(
    std::ostream& output, const organ::cm_incidence_receipt& value) noexcept;

}  // namespace holonics::tests
