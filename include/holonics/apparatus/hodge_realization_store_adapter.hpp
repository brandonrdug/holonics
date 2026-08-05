#pragma once

#include <holonics/exact/word.hpp>
#include <holonics/organ/hodge_realization_schema.hpp>

namespace holonics::event {
struct expression_geometry_rest_record;
struct hodge_realization_rest_record;
}

namespace holonics::apparatus {

enum class hodge_store_status : std::uint8_t {
  returned, invalid_aperture, open_refused, size_refused, transfer_refused, parse_refused
};

struct hodge_store_receipt final {
  hodge_store_status state{hodge_store_status::invalid_aperture};
  exact::word bytes{}; exact::word transfer_calls{};
  std::uint64_t byte_fold{}; std::uint64_t path_fold{}; bool integrity_exact{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == hodge_store_status::returned;
  }
};

[[nodiscard]] hodge_store_receipt read_hodge_realization_card(
    const char* path, organ::hodge_realization_card& card) noexcept;
[[nodiscard]] hodge_store_receipt read_expression_geometry_handoff(
    const char* path, event::expression_geometry_rest_record& record) noexcept;
[[nodiscard]] hodge_store_receipt write_hodge_realization_handoff(
    const char* path, const event::hodge_realization_rest_record& record) noexcept;
[[nodiscard]] hodge_store_receipt read_hodge_realization_handoff(
    const char* path, event::hodge_realization_rest_record& record) noexcept;

}  // namespace holonics::apparatus
