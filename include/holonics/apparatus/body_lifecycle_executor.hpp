#pragma once

#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/lifecycle_schema.hpp>

namespace holonics::apparatus {

struct body_lifecycle_input final {
  body::rest_region regions[body::live_region_capacity]{};
  event::deed_request request{};
  std::uint64_t returned_payload{};
};

enum class body_lifecycle_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct body_lifecycle_executor_receipt final {
  body_lifecycle_executor_status state{body_lifecycle_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_body_bytes{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == body_lifecycle_executor_status::returned;
  }
};

[[nodiscard]] body_lifecycle_executor_receipt execute_body_lifecycle(
    const body_lifecycle_input& input,
    event::lifecycle_output& output) noexcept;

}  // namespace holonics::apparatus
