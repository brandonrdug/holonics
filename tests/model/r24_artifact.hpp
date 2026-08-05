#pragma once

#include <iosfwd>

#include "r24_verify.hpp"

namespace holonics::tests {

void write_r24_artifact(std::ostream& output,
    const apparatus::variation_store_receipt& card_load,
    const apparatus::variation_store_receipt& rest_load,
    const apparatus::variation_store_receipt& rest_write,
    const apparatus::variation_executor_receipt& execution,
    const apparatus::variation_probe_receipt& probe,
    const organ::algebraic_variation_receipt& changed,
    const event::algebraic_variation_observation& value,
    const event::algebraic_variation_rest_record& handoff,
    std::size_t failures) noexcept;
void write_r24_atlas(std::ostream& output,
    const organ::algebraic_variation_receipt& value) noexcept;

}  // namespace holonics::tests
