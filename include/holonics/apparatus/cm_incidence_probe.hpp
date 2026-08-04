#pragma once

#include <holonics/organ/cm_incidence_receipt.hpp>

namespace holonics::apparatus {

enum class cm_probe_status : std::uint8_t {
  returned,
  invalid_foundation,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  derivation_refused
};

struct cm_probe_receipt final {
  cm_probe_status state{cm_probe_status::invalid_foundation};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word kernel_launches{};
  exact::word launched_threads{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == cm_probe_status::returned;
  }
};

[[nodiscard]] cm_probe_receipt probe_cm_derivation(
    const organ::cm_incidence_foundation& foundation,
    organ::cm_incidence_receipt& returned) noexcept;

}  // namespace holonics::apparatus
