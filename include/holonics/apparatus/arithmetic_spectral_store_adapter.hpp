#pragma once

#include <holonics/exact/word.hpp>
#include <holonics/organ/arithmetic_spectral_schema.hpp>

namespace holonics::event {
struct hodge_realization_rest_record;
struct arithmetic_spectral_rest_record;
}

namespace holonics::apparatus {

enum class arithmetic_store_status : std::uint8_t {
  returned, invalid_aperture, open_refused, size_refused, transfer_refused, parse_refused
};

struct arithmetic_store_receipt final {
  arithmetic_store_status state{arithmetic_store_status::invalid_aperture};
  exact::word bytes{}; exact::word transfer_calls{};
  std::uint64_t byte_fold{}; std::uint64_t path_fold{}; bool integrity_exact{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == arithmetic_store_status::returned;
  }
};

[[nodiscard]] arithmetic_store_receipt read_arithmetic_spectral_card(
    const char* path, organ::arithmetic_spectral_card& card) noexcept;
[[nodiscard]] arithmetic_store_receipt read_hodge_spectral_handoff(
    const char* path, event::hodge_realization_rest_record& record) noexcept;
[[nodiscard]] arithmetic_store_receipt write_arithmetic_spectral_handoff(
    const char* path, const event::arithmetic_spectral_rest_record& record) noexcept;
[[nodiscard]] arithmetic_store_receipt read_arithmetic_spectral_handoff(
    const char* path, event::arithmetic_spectral_rest_record& record) noexcept;

}  // namespace holonics::apparatus
