#pragma once

#include <holonics/apparatus/characteristic_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::characteristic_mount r19_case(
    const event::phase_crystal_rest_record& inherited) noexcept;
[[nodiscard]] event::phase_crystal_rest_record r19_host_phase_rest() noexcept;

}  // namespace holonics::tests
