#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/weave_executor.hpp>

namespace holonics::tests {

void write_r6_artifact(std::ostream& output,
    const apparatus::weave_executor_receipt& execution,
    const apparatus::weave_batch_observation& observation,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
