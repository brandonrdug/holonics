#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_phase_crystal_return.hpp>

namespace holonics::apparatus {

enum class phase_crystal_executor_status : std::uint8_t {
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

struct phase_crystal_mount final {
  organ::phase_crystal_foundation foundation{};
  organ::phase_crystal_question question{};
  event::geometry_inquiry_rest_record inherited{};
};

struct phase_crystal_executor_receipt final {
  phase_crystal_executor_status state{phase_crystal_executor_status::invalid_aperture};
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
    return state == phase_crystal_executor_status::returned;
  }
};

[[nodiscard]] phase_crystal_executor_receipt execute_phase_crystal(
    const phase_crystal_mount& mount,
    const lean_process_configuration& process,
    event::phase_crystal_observation& observation,
    event::phase_crystal_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
