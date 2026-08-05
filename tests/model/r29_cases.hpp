#pragma once

#include <holonics/apparatus/arithmetic_spectral_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::arithmetic_spectral_mount r29_case(
    const event::hodge_realization_rest_record& inherited,
    const organ::arithmetic_spectral_card& card) noexcept;
[[nodiscard]] organ::arithmetic_spectral_card r29_host_card() noexcept;

}  // namespace holonics::tests
