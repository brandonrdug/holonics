#pragma once

#include <cstdint>

#include <holonics/apparatus/generative_math_receipt.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class generative_math_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct generative_math_executor_receipt final {
  generative_math_executor_status state{generative_math_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word mounted_answer_bytes{};
  exact::word external_checker_calls{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  exact::word host_semantic_events{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == generative_math_executor_status::returned;
  }
};

[[nodiscard]] generative_math_executor_receipt execute_generative_math(
    const generative_math_mount& mount, generative_math_observation& observation) noexcept;

}  // namespace holonics::apparatus
