#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/receiver_geometry_executor.hpp>

namespace holonics::tests {

void write_r7_artifact(std::ostream& output,
    const apparatus::receiver_geometry_executor_receipt& execution,
    const apparatus::receiver_geometry_observation& observation,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
