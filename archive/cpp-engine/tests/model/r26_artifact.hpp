#pragma once

#include <iosfwd>

#include "r26_verify.hpp"

namespace holonics::tests {

void write_r26_artifact(std::ostream& output, bool sources_loaded,
    const apparatus::intrinsic_hypergeometry_store_receipt& card_load,
    const apparatus::intrinsic_hypergeometry_store_receipt& rest_load,
    const apparatus::intrinsic_hypergeometry_store_receipt& rest_write,
    const apparatus::intrinsic_hypergeometry_executor_receipt& execution,
    const event::intrinsic_hypergeometry_observation& value,
    const event::intrinsic_hypergeometry_rest_record& handoff,
    std::size_t failures) noexcept;
void write_r26_atlas(std::ostream& output,
    const event::intrinsic_hypergeometry_observation& value) noexcept;

}  // namespace holonics::tests
