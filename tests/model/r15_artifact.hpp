#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/return_conditioning_executor.hpp>
#include <holonics/apparatus/theorem_rest_store_adapter.hpp>

namespace holonics::tests {

void write_r15_artifact(std::ostream& output,
    const apparatus::theorem_rest_store_receipt& load,
    const apparatus::return_conditioning_executor_receipt& execution,
    const event::return_conditioning_observation& value,
    const event::theorem_production_rest_record& handoff,
    const event::dependent_theorem_setup& setup,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
