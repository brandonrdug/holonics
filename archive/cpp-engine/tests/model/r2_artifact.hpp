#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/structure_executor.hpp>

#include "r2_cases.hpp"

namespace holonics::tests {

void write_r2_artifact(
    std::ostream& stream,
    const apparatus::structure_executor_receipt& execution,
    const r2_output_batch& outputs,
    std::size_t verification_failures);

}  // namespace holonics::tests
