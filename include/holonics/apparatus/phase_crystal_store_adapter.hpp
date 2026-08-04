#pragma once

#include <cstdint>

#include <holonics/event/phase_crystal_rest.hpp>

namespace holonics::apparatus {

enum class phase_crystal_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  transfer_refused,
  size_refused,
  integrity_refused
};

struct phase_crystal_store_receipt final {
  phase_crystal_store_status state{phase_crystal_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  exact::word source_bytes{};
  exact::word retrieval_handles{};
  bool integrity_exact{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == phase_crystal_store_status::returned;
  }
};

[[nodiscard]] phase_crystal_store_receipt read_geometry_inquiry_rest(
    const char* path, event::geometry_inquiry_rest_record& record) noexcept;
[[nodiscard]] phase_crystal_store_receipt write_phase_crystal_rest(
    const char* path, const event::phase_crystal_rest_record& record) noexcept;

}  // namespace holonics::apparatus
