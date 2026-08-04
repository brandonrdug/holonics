#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_geometry_inquiry_return.hpp>

namespace holonics::apparatus {

enum class geometry_inquiry_executor_status : std::uint8_t {
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

struct geometry_inquiry_mount final {
  organ::geometry_inquiry_foundation foundation{};
  organ::geometry_inquiry_question question{};
  event::terminal_theorem_rest_record inherited{};
};

struct geometry_inquiry_executor_receipt final {
  geometry_inquiry_executor_status state{geometry_inquiry_executor_status::invalid_aperture};
  lean_process_receipt process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word probe_threads{};
  exact::word host_semantic_events{};
  exact::word engine_source_reads{};
  exact::word exterior_retrieval_calls{};
  exact::word developmental_source_bytes{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == geometry_inquiry_executor_status::returned;
  }
};

[[nodiscard]] geometry_inquiry_executor_receipt execute_geometry_inquiry(
    const geometry_inquiry_mount& mount,
    const lean_process_configuration& process,
    event::geometry_inquiry_observation& observation,
    event::geometry_inquiry_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
