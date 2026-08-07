#pragma once

#include <cstddef>

#include <holonics/apparatus/intrinsic_hypergeometry_executor.hpp>
#include <holonics/apparatus/intrinsic_hypergeometry_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r26_verification_failures(bool sources_loaded,
    const apparatus::intrinsic_hypergeometry_store_receipt& rest_load,
    const apparatus::intrinsic_hypergeometry_executor_receipt& execution,
    const event::intrinsic_hypergeometry_observation& actual,
    const event::intrinsic_hypergeometry_rest_record& handoff) noexcept;

}  // namespace holonics::tests
