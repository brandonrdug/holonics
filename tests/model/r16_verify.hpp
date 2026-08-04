#pragma once

#include <cstddef>

#include <holonics/apparatus/terminal_bundle_store_adapter.hpp>
#include <holonics/apparatus/terminal_theorem_executor.hpp>
#include <holonics/apparatus/theorem_rest_store_adapter.hpp>

namespace holonics::tests {

[[nodiscard]] std::size_t r16_verification_failures(
    const apparatus::theorem_rest_store_receipt& rest_load,
    const apparatus::dependent_setup_store_receipt& setup_load,
    apparatus::terminal_store_status first_collection,
    const apparatus::first_return_artifact_testimony& first,
    const apparatus::terminal_theorem_executor_receipt& execution,
    const event::terminal_theorem_observation& actual,
    const event::terminal_theorem_rest_record& handoff) noexcept;

}  // namespace holonics::tests
