#pragma once

#include <cstddef>

#include "r2_cases.hpp"

namespace holonics::tests {

[[nodiscard]] std::size_t r2_verification_failures(
    const r2_input_batch& inputs,
    const r2_output_batch& outputs) noexcept;

}  // namespace holonics::tests
