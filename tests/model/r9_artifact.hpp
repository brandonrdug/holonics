#pragma once

#include <cstddef>
#include <iosfwd>

#include <holonics/apparatus/reflective_codec_executor.hpp>

namespace holonics::tests {

void write_r9_artifact(
    std::ostream& output,
    const apparatus::reflective_codec_executor_receipt& execution,
    const apparatus::reflective_codec_observation& observation,
    std::size_t failures) noexcept;

}  // namespace holonics::tests
