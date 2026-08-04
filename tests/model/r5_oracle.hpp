#pragma once

#include <holonics/current/current_receipt.hpp>

namespace holonics::tests {

[[nodiscard]] current::current_batch_observation r5_oracle(
    const current::current_mount_batch& mount) noexcept;

}  // namespace holonics::tests
