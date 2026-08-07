#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_regular_singular_return.hpp>

namespace holonics::apparatus {

enum class regular_singular_executor_status : std::uint8_t {
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

struct regular_singular_mount final {
  organ::regular_singular_foundation foundation{};
  organ::regular_singular_question question{};
  event::characteristic_rest_record inherited{};
};

struct regular_singular_executor_receipt final {
  regular_singular_executor_status state{regular_singular_executor_status::invalid_aperture};
  lean_process_receipt process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word chart_threads{};
  exact::word coefficient_threads{};
  exact::word host_semantic_events{};
  exact::word engine_source_reads{};
  exact::word exterior_retrieval_calls{};
  exact::word historical_renderer_bytes{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == regular_singular_executor_status::returned;
  }
};

[[nodiscard]] regular_singular_executor_receipt execute_regular_singular(
    const regular_singular_mount& mount,
    const lean_process_configuration& process,
    event::regular_singular_observation& observation,
    event::regular_singular_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
