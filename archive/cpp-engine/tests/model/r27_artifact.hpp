#pragma once

#include <iosfwd>

#include <holonics/apparatus/expression_geometry_executor.hpp>
#include <holonics/apparatus/expression_geometry_store_adapter.hpp>

namespace holonics::tests {

void write_r27_artifact(std::ostream& out, bool source_loaded,
    const apparatus::expression_geometry_store_receipt& source_load,
    const apparatus::expression_geometry_store_receipt& rest_load,
    const apparatus::expression_geometry_store_receipt& rest_write,
    const apparatus::expression_geometry_executor_receipt& execution,
    const event::expression_geometry_observation& observation,
    const event::expression_geometry_rest_record& handoff,
    std::size_t failures);

}  // namespace holonics::tests
