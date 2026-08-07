#pragma once

#include <holonics/apparatus/regular_singular_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::regular_singular_mount r20_case(
    const event::characteristic_rest_record& inherited) noexcept;
[[nodiscard]] event::characteristic_rest_record r20_host_characteristic_rest() noexcept;

}  // namespace holonics::tests
