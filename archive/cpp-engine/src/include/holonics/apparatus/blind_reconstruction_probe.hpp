#pragma once

#include <cstdint>

#include <holonics/organ/blind_reconstruction_receipt.hpp>

namespace holonics::apparatus {

enum class blind_probe_status : std::uint8_t {
  returned,
  invalid_foundation,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  derivation_refused
};

struct blind_probe_receipt final {
  blind_probe_status state{blind_probe_status::invalid_foundation};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word kernel_launches{};
  exact::word launched_threads{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == blind_probe_status::returned;
  }
};

[[nodiscard]] blind_probe_receipt probe_blind_derivation(
    const organ::blind_reconstruction_foundation& foundation,
    organ::blind_reconstruction_receipt& returned) noexcept;

}  // namespace holonics::apparatus
