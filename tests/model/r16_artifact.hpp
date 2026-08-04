#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/terminal_bundle_store_adapter.hpp>
#include <holonics/apparatus/terminal_theorem_executor.hpp>
#include <holonics/apparatus/theorem_rest_store_adapter.hpp>

namespace holonics::tests {

void write_r16_artifact(std::ostream& output,
    const apparatus::theorem_rest_store_receipt& rest_load,
    const apparatus::dependent_setup_store_receipt& setup_load,
    const apparatus::first_return_artifact_testimony& first,
    const apparatus::terminal_theorem_executor_receipt& execution,
    const event::terminal_theorem_observation& value,
    const event::terminal_theorem_rest_record& handoff,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
