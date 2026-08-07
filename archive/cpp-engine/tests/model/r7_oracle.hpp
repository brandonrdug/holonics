#pragma once

#include <holonics/apparatus/receiver_geometry_receipt.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::receiver_geometry_observation r7_oracle(
    const apparatus::receiver_geometry_mount& mount) noexcept;

}  // namespace holonics::tests
