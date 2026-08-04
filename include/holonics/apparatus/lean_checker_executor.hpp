#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>

namespace holonics::apparatus {

enum class lean_checker_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  stage_refused,
  process_refused,
  resume_refused
};

struct lean_checker_mount final {
  codec::formal_math_face source{};
  body::rest_region regions[body::live_region_capacity]{};
  std::uint64_t body_seed{};
  std::uint64_t mathematical_morphology{};
  std::uint64_t codec_morphology{};
};

struct lean_checker_executor_receipt final {
  lean_checker_executor_status state{lean_checker_executor_status::invalid_aperture};
  lean_process_receipt process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word host_semantic_events{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == lean_checker_executor_status::returned;
  }
};

[[nodiscard]] lean_checker_executor_receipt execute_lean_checker(
    const lean_checker_mount& mount,
    const lean_process_configuration& process,
    event::checker_observation& observation) noexcept;

}  // namespace holonics::apparatus
