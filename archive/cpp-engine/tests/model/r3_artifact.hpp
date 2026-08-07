#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/source_store_adapter.hpp>
#include <holonics/apparatus/source_topology_executor.hpp>

namespace holonics::tests {

void write_r3_artifact(
    std::ostream& output,
    const char* const* source_paths,
    std::size_t source_count,
    const apparatus::source_store_receipt& original_store,
    const apparatus::source_store_receipt& relocated_store,
    std::size_t environment_failures,
    const apparatus::source_topology_executor_receipt& execution,
    const apparatus::source_topology_output& returned,
    std::size_t verification_failures);

}  // namespace holonics::tests
