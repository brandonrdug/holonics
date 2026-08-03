#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/exact_executor.hpp>

#include "r1_cases.hpp"

namespace holonics::tests {

void write_r1_artifact(
    std::ostream& stream,
    const apparatus::exact_executor_receipt& execution,
    const r1_output_batch& outputs,
    std::size_t parity_failures,
    std::size_t algebraic_failures,
    std::size_t exact_returns);

}  // namespace holonics::tests
