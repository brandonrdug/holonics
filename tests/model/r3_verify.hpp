#pragma once

#include <cstddef>

#include <holonics/apparatus/source_store_adapter.hpp>
#include <holonics/apparatus/source_topology_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::source_topology_output r3_oracle(
    const codec::source_environment& environment) noexcept;

[[nodiscard]] std::size_t r3_environment_failures(
    const codec::source_environment& original,
    const codec::source_environment& relocated,
    const apparatus::source_store_receipt& original_receipt,
    const apparatus::source_store_receipt& relocated_receipt) noexcept;

[[nodiscard]] std::size_t r3_verification_failures(
    const apparatus::source_topology_output& expected,
    const apparatus::source_topology_output& returned,
    const apparatus::source_topology_executor_receipt& execution) noexcept;

}  // namespace holonics::tests
