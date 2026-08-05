#pragma once

#include <holonics/event/intrinsic_hypergeometry_rest.hpp>

namespace holonics::apparatus {

enum class intrinsic_hypergeometry_store_status : std::uint8_t {
  returned, invalid_aperture, open_refused, transfer_refused, size_refused,
  parse_refused, integrity_refused
};

struct intrinsic_hypergeometry_store_receipt final {
  intrinsic_hypergeometry_store_status state{
      intrinsic_hypergeometry_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  bool integrity_exact{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == intrinsic_hypergeometry_store_status::returned;
  }
};

[[nodiscard]] intrinsic_hypergeometry_store_receipt read_intrinsic_hypergeometry_card(
    const char* path, organ::intrinsic_hypergeometry_card& card) noexcept;
[[nodiscard]] intrinsic_hypergeometry_store_receipt read_causal_linear_handoff(
    const char* path, event::causal_linear_rest_record& record) noexcept;
[[nodiscard]] intrinsic_hypergeometry_store_receipt write_intrinsic_hypergeometry_handoff(
    const char* path, const event::intrinsic_hypergeometry_rest_record& record) noexcept;

}  // namespace holonics::apparatus
