#pragma once

#include <holonics/apparatus/weave_receipt.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::weave_batch_observation r6_oracle(
    const current::weave_mount_batch& mount) noexcept;

}  // namespace holonics::tests
