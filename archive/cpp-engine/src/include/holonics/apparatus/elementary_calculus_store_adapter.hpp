#pragma once

#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>
#include <holonics/event/elementary_calculus_rest.hpp>

namespace holonics::apparatus {

[[nodiscard]] cultivated_store_receipt read_occurrence_incidence_card(
    const char *, organ::occurrence_incidence_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_composition_card(
    const char *, organ::composition_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_receiver_card(
    const char *, organ::receiver_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_local_chart_card(
    const char *, organ::local_chart_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_return_conduct_card(
    const char *, organ::return_conduct_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_heldout_triangle_card(
    const char *, organ::heldout_triangle_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_elementary_calculus_rest(
    const char *, event::elementary_calculus_rest_record &) noexcept;
[[nodiscard]] cultivated_store_receipt write_elementary_calculus_rest(
    const char *, const event::elementary_calculus_rest_record &) noexcept;

}  // namespace holonics::apparatus
