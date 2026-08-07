#pragma once

#include <cstddef>

#include <holonics/apparatus/mathematical_ecology_executor.hpp>
#include <holonics/apparatus/mathematical_source_adapter.hpp>

#include "r11_oracle.hpp"

namespace holonics::tests {

[[nodiscard]] std::size_t r11_verification_failures(
    const apparatus::mathematical_ecology_executor_receipt& execution,
    const apparatus::mathematical_ecology_observation& actual,
    const apparatus::mathematical_source_receipt& original,
    const apparatus::mathematical_source_receipt& relocated,
    bool exact_material,
    bool sources_detached,
    const r11_expected& expected) noexcept;

}  // namespace holonics::tests
