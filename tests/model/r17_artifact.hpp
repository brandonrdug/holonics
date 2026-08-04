#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/geometry_inquiry_store_adapter.hpp>
#include <holonics/apparatus/sealed_geometry_reference_adapter.hpp>
#include <holonics/apparatus/geometry_inquiry_executor.hpp>

namespace holonics::tests {

void write_r17_artifact(std::ostream& output,
    const apparatus::geometry_store_receipt& rest_load,
    const apparatus::geometry_store_receipt& rest_write,
    const apparatus::geometry_inquiry_executor_receipt& execution,
    const event::geometry_inquiry_observation& value,
    const event::geometry_inquiry_rest_record& handoff,
    const apparatus::sealed_geometry_comparison& comparison,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
