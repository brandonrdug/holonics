#pragma once

#include <cstdint>

#include <holonics/apparatus/conditioning_receipt.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class conditioning_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct conditioning_executor_receipt final {
  conditioning_executor_status state{conditioning_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word passage_bytes_after_training{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  exact::word host_semantic_events{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == conditioning_executor_status::returned;
  }
};

[[nodiscard]] conditioning_executor_receipt execute_conditioning(
    const conditioning_mount& mount,
    conditioning_observation& observation) noexcept;

}  // namespace holonics::apparatus
