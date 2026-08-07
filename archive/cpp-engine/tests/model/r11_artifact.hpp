#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/mathematical_ecology_executor.hpp>
#include <holonics/apparatus/mathematical_source_adapter.hpp>

namespace holonics::tests {

void write_r11_artifact(std::ostream& output,
    const apparatus::mathematical_ecology_executor_receipt& execution,
    const apparatus::mathematical_ecology_observation& value,
    const apparatus::mathematical_source_receipt& original,
    const apparatus::mathematical_source_receipt& relocated,
    bool exact_material,
    bool sources_detached,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
