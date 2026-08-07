#pragma once

#include <iosfwd>

#include "r21_verify.hpp"

namespace holonics::tests {

void write_r21_atlas(std::ostream& output,
    const organ::blind_reconstruction_receipt& value) noexcept;
void write_r21_artifact(std::ostream& output,
    const apparatus::blind_store_receipt& code_load,
    const apparatus::blind_store_receipt& moment_load,
    const apparatus::blind_store_receipt& rest_load,
    const apparatus::blind_store_receipt& rest_write,
    const apparatus::blind_reconstruction_executor_receipt& execution,
    const apparatus::blind_probe_receipt& code_probe,
    const apparatus::blind_probe_receipt& moment_probe,
    const event::blind_reconstruction_observation& value,
    const event::blind_reconstruction_rest_record& handoff,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
