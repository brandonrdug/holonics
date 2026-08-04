#pragma once

#include <cstdint>

#include <holonics/apparatus/mathematical_ecology_receipt.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class mathematical_ecology_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct mathematical_ecology_executor_receipt final {
  mathematical_ecology_executor_status state{
      mathematical_ecology_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word source_bytes_after_mount{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  exact::word host_semantic_events{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == mathematical_ecology_executor_status::returned;
  }
};

[[nodiscard]] mathematical_ecology_executor_receipt execute_mathematical_ecology(
    const mathematical_ecology_mount& mount,
    mathematical_ecology_observation& observation) noexcept;

}  // namespace holonics::apparatus
