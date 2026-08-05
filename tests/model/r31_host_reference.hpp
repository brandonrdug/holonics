#pragma once

#include <holonics/organ/cultivated_organ_receipt.hpp>

namespace holonics::tests {

void r31_development_cards(
    organ::developmental_stream_card (&cards)[organ::cultivation_family_count]) noexcept;
[[nodiscard]] organ::feature_geometry_receipt r31_reference_candidate(
    const organ::developmental_stream_card &, std::uint8_t, std::uint8_t) noexcept;
[[nodiscard]] std::size_t r31_heldout_reference_failures() noexcept;

}  // namespace holonics::tests
