#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/causal_current_executor.hpp>

namespace holonics::tests {

void write_r5_artifact(std::ostream& output,
    const apparatus::causal_current_executor_receipt& execution,
    const current::current_batch_observation& observation,
    const apparatus::causal_current_executor_receipt& unavailable,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
