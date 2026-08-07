#pragma once

#include <holonics/organ/toric_cycle_receipt.hpp>

namespace holonics::apparatus {

enum class toric_probe_status : std::uint8_t {
  returned,
  invalid_foundation,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  derivation_refused
};

struct toric_probe_receipt final {
  toric_probe_status state{toric_probe_status::invalid_foundation};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == toric_probe_status::returned;
  }
};

[[nodiscard]] toric_probe_receipt probe_toric_derivation(
    const organ::toric_cycle_foundation& foundation,
    organ::toric_cycle_receipt& returned) noexcept;

}  // namespace holonics::apparatus
