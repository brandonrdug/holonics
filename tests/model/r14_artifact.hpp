#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/theorem_production_executor.hpp>

namespace holonics::tests {

void write_r14_artifact(std::ostream& output,
    const apparatus::theorem_production_executor_receipt& execution,
    const event::theorem_production_observation& value,
    const event::theorem_production_rest_record& handoff,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
