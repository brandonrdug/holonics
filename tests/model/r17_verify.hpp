#pragma once

#include <cstddef>

#include <holonics/apparatus/geometry_inquiry_store_adapter.hpp>
#include <holonics/apparatus/sealed_geometry_reference_adapter.hpp>
#include <holonics/apparatus/geometry_inquiry_executor.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r17_verification_failures(
    const apparatus::geometry_store_receipt& rest_load,
    const apparatus::geometry_inquiry_executor_receipt& execution,
    const event::geometry_inquiry_observation& actual,
    const event::geometry_inquiry_rest_record& handoff,
    const apparatus::sealed_geometry_comparison& comparison) noexcept;

}  // namespace holonics::tests
