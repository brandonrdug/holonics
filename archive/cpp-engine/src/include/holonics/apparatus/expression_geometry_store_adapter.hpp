#pragma once

#include <holonics/exact/word.hpp>
#include <holonics/organ/expression_geometry_schema.hpp>

namespace holonics::event {
struct expression_geometry_rest_record;
struct intrinsic_hypergeometry_rest_record;
}

namespace holonics::apparatus {

enum class expression_geometry_store_status : std::uint8_t {
  returned, invalid_aperture, open_refused, size_refused, transfer_refused, parse_refused
};

struct expression_geometry_store_receipt final {
  expression_geometry_store_status state{expression_geometry_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  bool integrity_exact{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == expression_geometry_store_status::returned;
  }
};

[[nodiscard]] expression_geometry_store_receipt read_expression_geometry_card(
    const char* path, organ::expression_geometry_card& card) noexcept;
[[nodiscard]] expression_geometry_store_receipt read_intrinsic_hypergeometry_handoff(
    const char* path, event::intrinsic_hypergeometry_rest_record& record) noexcept;
[[nodiscard]] expression_geometry_store_receipt write_expression_geometry_handoff(
    const char* path, const event::expression_geometry_rest_record& record) noexcept;
[[nodiscard]] expression_geometry_store_receipt read_expression_geometry_handoff(
    const char* path, event::expression_geometry_rest_record& record) noexcept;

}  // namespace holonics::apparatus
