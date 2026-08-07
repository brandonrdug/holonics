#pragma once

#include <holonics/apparatus/phase_crystal_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::phase_crystal_mount r18_case(
    const event::geometry_inquiry_rest_record& inherited) noexcept;
[[nodiscard]] event::geometry_inquiry_rest_record r18_host_geometry_rest() noexcept;

}  // namespace holonics::tests
