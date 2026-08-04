#pragma once

#include <array>
#include <cstddef>

#include <holonics/structure/complex_schema.hpp>

namespace holonics::tests {

inline constexpr std::size_t r2_case_count = 10;
using r2_input_batch = std::array<structure::structure_case, r2_case_count>;
using r2_output_batch = std::array<structure::structure_output, r2_case_count>;

[[nodiscard]] r2_input_batch r2_cases();

}  // namespace holonics::tests
