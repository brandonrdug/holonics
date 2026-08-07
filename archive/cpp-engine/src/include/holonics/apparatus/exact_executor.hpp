#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/exact/deed.hpp>

namespace holonics::apparatus {

enum class executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct exact_deed_batch final {
  const exact::deed_input* inputs{};
  exact::deed_output* outputs{};
  std::size_t count{};
};

struct exact_executor_receipt final {
  executor_status state{executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word launched_threads{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == executor_status::returned;
  }
};

[[nodiscard]] exact_executor_receipt execute_exact_deeds(exact_deed_batch batch) noexcept;

}  // namespace holonics::apparatus
