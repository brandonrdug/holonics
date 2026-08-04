#pragma once

#include <holonics/apparatus/geometry_inquiry_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::geometry_inquiry_mount r17_case(
    const event::terminal_theorem_rest_record& inherited) noexcept;

[[nodiscard]] event::terminal_theorem_rest_record r17_host_terminal_rest() noexcept;

}  // namespace holonics::tests
