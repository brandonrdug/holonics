#pragma once

#include <cstdint>

#include <holonics/event/theorem_production_rest.hpp>

namespace holonics::apparatus {

enum class theorem_rest_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  read_refused,
  size_refused,
  integrity_refused
};

struct theorem_rest_store_receipt final {
  theorem_rest_store_status state{theorem_rest_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word read_calls{};
  exact::word developmental_source_bytes{};
  exact::word retrieval_handles{};
  bool integrity_exact{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == theorem_rest_store_status::returned;
  }
};

[[nodiscard]] theorem_rest_store_receipt read_theorem_production_rest(
    const char* path, event::theorem_production_rest_record& record) noexcept;

}  // namespace holonics::apparatus
