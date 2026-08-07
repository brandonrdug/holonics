#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/phase_crystal_executor.hpp>
#include <holonics/apparatus/phase_crystal_store_adapter.hpp>

namespace holonics::tests {

void write_r18_artifact(std::ostream& output,
    const apparatus::phase_crystal_store_receipt& rest_load,
    const apparatus::phase_crystal_store_receipt& rest_write,
    const apparatus::phase_crystal_executor_receipt& execution,
    const event::phase_crystal_observation& value,
    const event::phase_crystal_rest_record& handoff,
    std::size_t failures) noexcept;
void write_r18_atlas(std::ostream& output,
    const organ::phase_crystal_receipt& value) noexcept;

}  // namespace holonics::tests
