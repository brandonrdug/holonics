#pragma once

#include <cstdint>

#include <holonics/event/geometry_inquiry_rest.hpp>

namespace holonics::apparatus {

enum class geometry_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  transfer_refused,
  size_refused,
  integrity_refused
};

struct geometry_store_receipt final {
  geometry_store_status state{geometry_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  exact::word developmental_source_bytes{};
  exact::word retrieval_handles{};
  bool integrity_exact{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == geometry_store_status::returned;
  }
};

[[nodiscard]] geometry_store_receipt read_terminal_theorem_rest(
    const char* path, event::terminal_theorem_rest_record& record) noexcept;

[[nodiscard]] geometry_store_receipt write_geometry_inquiry_rest(
    const char* path, const event::geometry_inquiry_rest_record& record) noexcept;

}  // namespace holonics::apparatus
