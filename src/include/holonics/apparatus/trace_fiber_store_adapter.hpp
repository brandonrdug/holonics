#pragma once

#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>
#include <holonics/event/trace_fiber_rest.hpp>

namespace holonics::apparatus {

[[nodiscard]] cultivated_store_receipt
read_three_face_source_card(const char *, organ::three_face_source_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_heldout_oriented_system_card(
    const char *, organ::heldout_oriented_system_card &) noexcept;
[[nodiscard]] cultivated_store_receipt
read_trace_fiber_rest(const char *, event::trace_fiber_rest_record &) noexcept;
[[nodiscard]] cultivated_store_receipt
write_trace_fiber_rest(const char *,
                       const event::trace_fiber_rest_record &) noexcept;

} // namespace holonics::apparatus
