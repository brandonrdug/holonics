#pragma once

#include <holonics/apparatus/codec_store_adapter.hpp>
#include <holonics/apparatus/reflective_codec_receipt.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::reflective_codec_mount r9_case(
    const codec::codec_environment& environment,
    const apparatus::codec_store_receipt& original,
    const apparatus::codec_store_receipt& relocated) noexcept;

}  // namespace holonics::tests
