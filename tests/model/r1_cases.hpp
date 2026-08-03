#pragma once

#include <array>
#include <cstddef>

#include <holonics/exact/deed.hpp>

namespace holonics::tests {

inline constexpr std::size_t r1_case_count = 100;
using r1_input_batch = std::array<exact::deed_input, r1_case_count>;
using r1_output_batch = std::array<exact::deed_output, r1_case_count>;

[[nodiscard]] r1_input_batch r1_cases();
[[nodiscard]] bool r1_named_returns_hold(const r1_output_batch& outputs) noexcept;
[[nodiscard]] std::size_t r1_algebraic_failures(
    const r1_input_batch& inputs,
    const r1_output_batch& outputs) noexcept;

}  // namespace holonics::tests
