#pragma once

#include <cstdint>

#include <holonics/event/blind_reconstruction_rest.hpp>

namespace holonics::apparatus {

enum class blind_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  transfer_refused,
  size_refused,
  parse_refused,
  integrity_refused
};

struct blind_store_receipt final {
  blind_store_status state{blind_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  bool integrity_exact{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == blind_store_status::returned;
  }
};

[[nodiscard]] blind_store_receipt read_binary_code_card(
    const char* path, organ::binary_code_problem_card& card) noexcept;
[[nodiscard]] blind_store_receipt read_moment_problem_card(
    const char* path, organ::moment_problem_card& card) noexcept;
[[nodiscard]] blind_store_receipt read_regular_singular_handoff(
    const char* path, event::regular_singular_rest_record& record) noexcept;
[[nodiscard]] blind_store_receipt write_blind_reconstruction_handoff(
    const char* path, const event::blind_reconstruction_rest_record& record) noexcept;

}  // namespace holonics::apparatus
