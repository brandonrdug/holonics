#pragma once

#include <holonics/organ/causal_linear_receipt.hpp>

namespace holonics::apparatus {

enum class causal_linear_probe_status : std::uint8_t {
  returned, invalid_foundation, device_unavailable, allocation_refused,
  transfer_refused, derivation_refused
};

struct causal_linear_probe_receipt final {
  causal_linear_probe_status state{causal_linear_probe_status::invalid_foundation};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == causal_linear_probe_status::returned;
  }
};

[[nodiscard]] causal_linear_probe_receipt probe_causal_linear(
    const organ::causal_linear_foundation& foundation,
    organ::causal_linear_receipt& returned) noexcept;

}  // namespace holonics::apparatus
