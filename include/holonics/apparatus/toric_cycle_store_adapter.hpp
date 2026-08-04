#pragma once

#include <holonics/event/toric_cycle_rest.hpp>
#include <holonics/organ/toric_cycle_schema.hpp>

namespace holonics::apparatus {

enum class toric_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  transfer_refused,
  size_refused,
  parse_refused,
  integrity_refused
};

struct toric_store_receipt final {
  toric_store_status state{toric_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  bool integrity_exact{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == toric_store_status::returned;
  }
};

[[nodiscard]] toric_store_receipt read_toric_cycle_card(
    const char* path, organ::toric_cycle_card& card) noexcept;
[[nodiscard]] toric_store_receipt read_cm_incidence_handoff(
    const char* path, event::cm_incidence_rest_record& record) noexcept;
[[nodiscard]] toric_store_receipt write_toric_cycle_handoff(
    const char* path, const event::toric_cycle_rest_record& record) noexcept;

}  // namespace holonics::apparatus
