#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/lean_checker_executor.hpp>

namespace holonics::tests {

void write_r13_artifact(std::ostream& output,
    const apparatus::lean_checker_executor_receipt& execution,
    const event::checker_observation& value,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
