#pragma once

#include <cstddef>

#include <holonics/apparatus/blind_reconstruction_probe.hpp>
#include <holonics/apparatus/blind_reconstruction_store_adapter.hpp>

#include "r21_cases.hpp"

namespace holonics::tests {

[[nodiscard]] std::size_t r21_verification_failures(
    const apparatus::blind_store_receipt& code_load,
    const apparatus::blind_store_receipt& moment_load,
    const apparatus::blind_store_receipt& rest_load,
    const apparatus::blind_reconstruction_executor_receipt& execution,
    const apparatus::blind_probe_receipt& code_probe,
    const organ::blind_reconstruction_receipt& changed_code,
    const apparatus::blind_probe_receipt& moment_probe,
    const organ::blind_reconstruction_receipt& changed_moment,
    const event::blind_reconstruction_observation& actual,
    const event::blind_reconstruction_rest_record& handoff) noexcept;

}  // namespace holonics::tests
