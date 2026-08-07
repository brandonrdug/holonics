#pragma once

#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/apparatus/reflective_codec_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class reflective_codec_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct reflective_codec_executor_receipt final {
  reflective_codec_executor_status state{reflective_codec_executor_status::invalid_aperture};
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
    return state == reflective_codec_executor_status::returned;
  }
};

[[nodiscard]] reflective_codec_executor_receipt execute_reflective_codec(
    const reflective_codec_mount& mount,
    reflective_codec_observation& observation) noexcept;

}  // namespace holonics::apparatus
