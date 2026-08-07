#pragma once

#include <holonics/event/algebraic_variation_rest.hpp>
#include <holonics/organ/algebraic_variation_schema.hpp>

namespace holonics::apparatus {

enum class variation_store_status : std::uint8_t {
  returned, invalid_aperture, open_refused, transfer_refused, size_refused,
  parse_refused, integrity_refused
};

struct variation_store_receipt final {
  variation_store_status state{variation_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  bool integrity_exact{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == variation_store_status::returned;
  }
};

[[nodiscard]] variation_store_receipt read_algebraic_variation_card(
    const char* path, organ::algebraic_variation_card& card) noexcept;
[[nodiscard]] variation_store_receipt read_toric_cycle_handoff(
    const char* path, event::toric_cycle_rest_record& record) noexcept;
[[nodiscard]] variation_store_receipt write_algebraic_variation_handoff(
    const char* path, const event::algebraic_variation_rest_record& record) noexcept;

}  // namespace holonics::apparatus
