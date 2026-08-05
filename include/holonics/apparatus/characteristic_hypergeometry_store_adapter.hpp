#pragma once

#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>
#include <holonics/event/characteristic_hypergeometry_rest.hpp>

namespace holonics::apparatus {

[[nodiscard]] cultivated_store_receipt
read_transition_source_card(const char *,
                            organ::transition_source_card &) noexcept;
[[nodiscard]] cultivated_store_receipt
read_heldout_local_system_card(const char *,
                               organ::heldout_local_system_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_characteristic_rest(
    const char *, event::characteristic_hypergeometry_rest_record &) noexcept;
[[nodiscard]] cultivated_store_receipt write_characteristic_rest(
    const char *,
    const event::characteristic_hypergeometry_rest_record &) noexcept;

} // namespace holonics::apparatus
