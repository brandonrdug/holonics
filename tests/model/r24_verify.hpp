#pragma once

#include <cstddef>

#include <holonics/apparatus/algebraic_variation_executor.hpp>
#include <holonics/apparatus/algebraic_variation_probe.hpp>
#include <holonics/apparatus/algebraic_variation_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r24_verification_failures(
    const apparatus::variation_store_receipt& card_load,
    const apparatus::variation_store_receipt& rest_load,
    const apparatus::variation_executor_receipt& execution,
    const apparatus::variation_probe_receipt& probe,
    const organ::algebraic_variation_receipt& changed,
    const event::algebraic_variation_observation& actual,
    const event::algebraic_variation_rest_record& handoff) noexcept;

}  // namespace holonics::tests
