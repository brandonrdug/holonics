#pragma once

#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/apparatus/weave_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class weave_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct weave_executor_receipt final {
  weave_executor_status state{weave_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  exact::word host_semantic_events{};
  exact::word unchanged_retries{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == weave_executor_status::returned;
  }
};

[[nodiscard]] weave_executor_receipt execute_weave(
    const current::weave_mount_batch& mount,
    weave_batch_observation& observation) noexcept;

}  // namespace holonics::apparatus
