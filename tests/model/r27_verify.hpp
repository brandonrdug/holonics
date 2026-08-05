#pragma once

#include <cstddef>

#include <holonics/apparatus/expression_geometry_executor.hpp>
#include <holonics/apparatus/expression_geometry_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r27_verification_failures(bool source_loaded,
    const apparatus::expression_geometry_store_receipt& rest_load,
    const apparatus::expression_geometry_executor_receipt& execution,
    const event::expression_geometry_observation& actual,
    const event::expression_geometry_rest_record& handoff) noexcept;

}  // namespace holonics::tests
