#pragma once

#include <holonics/apparatus/arithmetic_spectral_store_adapter.hpp>
#include <holonics/event/cultivated_organ_rest.hpp>

namespace holonics::apparatus {

using cultivated_store_status = arithmetic_store_status;
using cultivated_store_receipt = arithmetic_store_receipt;

[[nodiscard]] cultivated_store_receipt read_developmental_stream_card(
    const char *, organ::developmental_stream_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_star_structure_card(
    const char *, organ::star_structure_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_walk_structure_card(
    const char *, organ::walk_structure_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_signed_carrier_card(
    const char *, organ::signed_carrier_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_graded_structure_card(
    const char *, organ::graded_structure_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_cultivated_organ_rest(
    const char *, event::cultivated_organ_rest_record &) noexcept;
[[nodiscard]] cultivated_store_receipt write_cultivated_organ_rest(
    const char *, const event::cultivated_organ_rest_record &) noexcept;

}  // namespace holonics::apparatus
