#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_characteristic_return.hpp>

namespace holonics::apparatus {

enum class characteristic_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  probe_refused,
  formation_refused,
  process_refused,
  return_refused,
  rest_refused
};

struct characteristic_mount final {
  organ::characteristic_foundation foundation{};
  organ::characteristic_question question{};
  event::phase_crystal_rest_record inherited{};
};

struct characteristic_executor_receipt final {
  characteristic_executor_status state{characteristic_executor_status::invalid_aperture};
  lean_process_receipt process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word case_threads{};
  exact::word host_semantic_events{};
  exact::word engine_source_reads{};
  exact::word exterior_retrieval_calls{};
  exact::word historical_renderer_bytes{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == characteristic_executor_status::returned;
  }
};

[[nodiscard]] characteristic_executor_receipt execute_characteristic(
    const characteristic_mount& mount,
    const lean_process_configuration& process,
    event::characteristic_observation& observation,
    event::characteristic_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
