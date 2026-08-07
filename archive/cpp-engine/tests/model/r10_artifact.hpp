#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/conditioning_executor.hpp>

namespace holonics::tests {
void write_r10_artifact(std::ostream& output,
    const apparatus::conditioning_executor_receipt& execution,
    const apparatus::conditioning_observation& observation,
    std::size_t failures) noexcept;
}  // namespace holonics::tests
