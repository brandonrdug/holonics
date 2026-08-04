#pragma once

#include <cstddef>

#include <holonics/apparatus/reflective_codec_executor.hpp>

#include "r9_oracle.hpp"

namespace holonics::tests {

[[nodiscard]] std::size_t r9_verification_failures(
    const apparatus::reflective_codec_executor_receipt& execution,
    const apparatus::reflective_codec_observation& actual,
    const r9_expected& expected) noexcept;

}  // namespace holonics::tests
