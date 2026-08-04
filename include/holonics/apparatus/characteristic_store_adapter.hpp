#pragma once

#include <cstdint>

#include <holonics/event/characteristic_rest.hpp>

namespace holonics::apparatus {

enum class characteristic_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  transfer_refused,
  size_refused,
  integrity_refused
};

struct characteristic_store_receipt final {
  characteristic_store_status state{characteristic_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  exact::word source_bytes{};
  exact::word retrieval_handles{};
  bool integrity_exact{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == characteristic_store_status::returned;
  }
};

[[nodiscard]] characteristic_store_receipt read_phase_crystal_rest(
    const char* path, event::phase_crystal_rest_record& record) noexcept;
[[nodiscard]] characteristic_store_receipt write_characteristic_rest(
    const char* path, const event::characteristic_rest_record& record) noexcept;

}  // namespace holonics::apparatus
