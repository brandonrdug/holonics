#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/generative_math_executor.hpp>

namespace holonics::tests {

void write_r12_artifact(std::ostream& output,
    const apparatus::generative_math_executor_receipt& execution,
    const apparatus::generative_math_observation& value,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
