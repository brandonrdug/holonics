#pragma once

#include <holonics/organ/algebraic_variation_receipt.hpp>

namespace holonics::apparatus {

enum class variation_probe_status : std::uint8_t {
  returned, invalid_foundation, device_unavailable, allocation_refused,
  transfer_refused, derivation_refused
};

struct variation_probe_receipt final {
  variation_probe_status state{variation_probe_status::invalid_foundation};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == variation_probe_status::returned;
  }
};

[[nodiscard]] variation_probe_receipt probe_algebraic_variation(
    const organ::algebraic_variation_foundation& foundation,
    organ::algebraic_variation_receipt& returned) noexcept;

}  // namespace holonics::apparatus
