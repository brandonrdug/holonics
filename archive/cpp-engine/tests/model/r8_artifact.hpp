#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/boundary_condensation_executor.hpp>

namespace holonics::tests {

void write_r8_artifact(std::ostream& output,
    const apparatus::boundary_condensation_executor_receipt& execution,
    const apparatus::boundary_condensation_observation& observation,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
