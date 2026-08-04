#pragma once

#include <holonics/apparatus/boundary_condensation_receipt.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::boundary_condensation_observation r8_oracle(
    const apparatus::boundary_condensation_mount& mount) noexcept;

}  // namespace holonics::tests
