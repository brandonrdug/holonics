#pragma once

#include <holonics/apparatus/terminal_theorem_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::terminal_theorem_mount r16_case(
    const event::theorem_production_rest_record& inherited,
    const event::dependent_theorem_setup& setup) noexcept;

[[nodiscard]] event::theorem_production_rest_record r16_host_rest() noexcept;
[[nodiscard]] event::dependent_theorem_setup r16_host_setup() noexcept;

}  // namespace holonics::tests
