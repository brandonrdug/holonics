#pragma once

#include <cstdint>

#include <holonics/apparatus/boundary_condensation_receipt.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class boundary_condensation_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct boundary_condensation_executor_receipt final {
  boundary_condensation_executor_status state{
      boundary_condensation_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  exact::word host_semantic_events{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == boundary_condensation_executor_status::returned;
  }
};

[[nodiscard]] boundary_condensation_executor_receipt execute_boundary_condensation(
    const boundary_condensation_mount& mount,
    boundary_condensation_observation& observation) noexcept;

}  // namespace holonics::apparatus
