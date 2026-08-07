#pragma once

#include <holonics/apparatus/elementary_calculus_resident.hpp>
#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>

namespace holonics::apparatus {

enum class elementary_executor_status : std::uint8_t {
  returned, invalid_mount, device_unavailable, allocation_refused, transfer_refused,
  formation_refused, checker_process_refused, checker_return_refused, rest_refused
};

struct elementary_executor_receipt final {
  elementary_executor_status state{elementary_executor_status::invalid_mount};
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
  [[nodiscard]] bool returned() const noexcept { return state == elementary_executor_status::returned; }
};

[[nodiscard]] elementary_executor_receipt execute_elementary_discovery(
    const elementary_discovery_mount &, const lean_process_configuration &,
    event::elementary_calculus_observation &, organ::elementary_workspace &,
    event::elementary_calculus_rest_record &) noexcept;
[[nodiscard]] elementary_executor_receipt execute_elementary_application(
    const elementary_application_mount &, const lean_process_configuration &,
    event::heldout_holonomy_observation &, organ::heldout_workspace &,
    event::elementary_calculus_rest_record &) noexcept;

}  // namespace holonics::apparatus
