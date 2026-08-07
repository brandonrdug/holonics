#pragma once

#include <holonics/event/causal_linear_rest.hpp>

namespace holonics::apparatus {

enum class causal_linear_store_status : std::uint8_t {
  returned, invalid_aperture, open_refused, transfer_refused, size_refused,
  parse_refused, integrity_refused
};

struct causal_linear_store_receipt final {
  causal_linear_store_status state{causal_linear_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  bool integrity_exact{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == causal_linear_store_status::returned;
  }
};

[[nodiscard]] causal_linear_store_receipt read_causal_linear_card(
    const char* path, organ::causal_linear_card& card) noexcept;
[[nodiscard]] causal_linear_store_receipt read_algebraic_variation_handoff(
    const char* path, event::algebraic_variation_rest_record& record) noexcept;
[[nodiscard]] causal_linear_store_receipt write_causal_linear_handoff(
    const char* path, const event::causal_linear_rest_record& record) noexcept;

}  // namespace holonics::apparatus
