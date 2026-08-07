#pragma once

#include <holonics/exact/deed.hpp>

namespace holonics::tests {

[[nodiscard]] exact::deed_output r1_oracle(const exact::deed_input& input);
[[nodiscard]] bool equal_deed_output(
    const exact::deed_output& left,
    const exact::deed_output& right) noexcept;

}  // namespace holonics::tests
