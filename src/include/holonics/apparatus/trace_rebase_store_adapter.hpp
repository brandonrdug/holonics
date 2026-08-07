#pragma once

#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>
#include <holonics/event/trace_rebase_rest.hpp>

namespace holonics::apparatus {

[[nodiscard]] cultivated_store_receipt read_trace_rebase_source_card(
    const char *, organ::trace_rebase_source_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_heldout_trace_rebase_card(
    const char *, organ::heldout_trace_rebase_card &) noexcept;
[[nodiscard]] cultivated_store_receipt read_trace_rebase_rest(
    const char *, event::trace_rebase_rest_record &) noexcept;
[[nodiscard]] cultivated_store_receipt write_trace_rebase_rest(
    const char *, const event::trace_rebase_rest_record &) noexcept;

} // namespace holonics::apparatus
