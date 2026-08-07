#pragma once

#include <holonics/event/cm_incidence_rest.hpp>
#include <holonics/organ/cm_incidence_schema.hpp>

namespace holonics::apparatus {

enum class cm_store_status : std::uint8_t {
  returned,
  invalid_aperture,
  open_refused,
  transfer_refused,
  size_refused,
  parse_refused,
  integrity_refused
};

struct cm_store_receipt final {
  cm_store_status state{cm_store_status::invalid_aperture};
  exact::word bytes{};
  exact::word transfer_calls{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  bool integrity_exact{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == cm_store_status::returned;
  }
};

[[nodiscard]] cm_store_receipt read_cm_problem_card(
    const char* path, organ::cm_problem_card& card) noexcept;
[[nodiscard]] cm_store_receipt read_blind_reconstruction_handoff(
    const char* path, event::blind_reconstruction_rest_record& record) noexcept;
[[nodiscard]] cm_store_receipt write_cm_incidence_handoff(
    const char* path, const event::cm_incidence_rest_record& record) noexcept;

}  // namespace holonics::apparatus
