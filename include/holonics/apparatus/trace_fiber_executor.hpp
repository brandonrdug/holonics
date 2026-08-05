#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/apparatus/trace_fiber_resident.hpp>

namespace holonics::apparatus {

enum class trace_fiber_executor_status : std::uint8_t {
  returned,
  invalid_mount,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  formation_refused,
  checker_process_refused,
  checker_return_refused,
  rest_refused
};
struct trace_fiber_executor_receipt final {
  trace_fiber_executor_status state{trace_fiber_executor_status::invalid_mount};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word semantic_threads{};
  exact::word host_semantic_events{};
  exact::word source_currents{};
  exact::word dependency_barriers{};
  lean_process_receipt checker{};
  physical_telemetry_receipt physical{};
  [[nodiscard]] bool returned() const noexcept {
    return state == trace_fiber_executor_status::returned;
  }
};
[[nodiscard]] trace_fiber_executor_receipt execute_trace_fiber_discovery(
    const trace_fiber_discovery_mount &, const lean_process_configuration &,
    event::trace_fiber_discovery_observation &, organ::trace_fiber_workspace &,
    event::trace_fiber_rest_record &) noexcept;
[[nodiscard]] trace_fiber_executor_receipt execute_trace_fiber_application(
    const trace_fiber_application_mount &, const lean_process_configuration &,
    event::heldout_trace_fiber_observation &,
    event::trace_fiber_rest_record &) noexcept;

} // namespace holonics::apparatus
