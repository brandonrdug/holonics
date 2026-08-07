#pragma once

#include <holonics/apparatus/characteristic_hypergeometry_resident.hpp>
#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>

namespace holonics::apparatus {

enum class characteristic_executor_status : std::uint8_t {
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
struct characteristic_executor_receipt final {
  characteristic_executor_status state{
      characteristic_executor_status::invalid_mount};
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
    return state == characteristic_executor_status::returned;
  }
};
[[nodiscard]] characteristic_executor_receipt execute_characteristic_discovery(
    const characteristic_discovery_mount &, const lean_process_configuration &,
    event::characteristic_discovery_observation &,
    organ::characteristic_workspace &,
    event::characteristic_hypergeometry_rest_record &) noexcept;
[[nodiscard]] characteristic_executor_receipt
execute_characteristic_application(
    const characteristic_application_mount &,
    const lean_process_configuration &,
    event::heldout_characteristic_observation &,
    event::characteristic_hypergeometry_rest_record &) noexcept;

} // namespace holonics::apparatus
