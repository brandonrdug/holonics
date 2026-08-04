#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/body_lifecycle_executor.hpp>

namespace holonics::tests {

void write_r4_artifact(
    std::ostream& stream,
    const apparatus::body_lifecycle_executor_receipt& execution,
    const event::lifecycle_output& output,
    std::size_t failures);

}  // namespace holonics::tests
