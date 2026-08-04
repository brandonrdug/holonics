#pragma once

#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/current_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class causal_current_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct causal_current_executor_receipt final {
  causal_current_executor_status state{causal_current_executor_status::invalid_aperture};
  current::current_obstruction obstruction{current::current_obstruction::none};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_body_bytes{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  exact::word host_semantic_candidates{};
  exact::word host_oracle_replays{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == causal_current_executor_status::returned;
  }
};

[[nodiscard]] causal_current_executor_receipt execute_causal_current(
    const current::current_mount_batch& mount,
    current::current_batch_observation& observation,
    std::uint32_t required_device_major,
    std::uint32_t required_device_minor) noexcept;

}  // namespace holonics::apparatus
