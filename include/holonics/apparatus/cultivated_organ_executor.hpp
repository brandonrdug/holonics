#pragma once

#include <holonics/apparatus/cultivated_organ_resident.hpp>
#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>

namespace holonics::apparatus {

enum class cultivated_executor_status : std::uint8_t {
  returned,
  invalid_mount,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  deed_refused,
  formation_refused,
  checker_process_refused,
  checker_return_refused,
  rest_refused
};

struct cultivated_executor_receipt final {
  cultivated_executor_status state{cultivated_executor_status::invalid_mount};
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
    return state == cultivated_executor_status::returned;
  }
};

[[nodiscard]] cultivated_executor_receipt execute_organ_cultivation(
    const cultivation_mount &, const lean_process_configuration &,
    event::cultivation_observation &, organ::cultivation_workspace &,
    event::cultivated_organ_rest_record &) noexcept;
[[nodiscard]] cultivated_executor_receipt execute_cultivated_application(
    const cultivated_application_mount &, const lean_process_configuration &,
    event::cultivated_application_observation &,
    event::cultivated_organ_rest_record &) noexcept;

}  // namespace holonics::apparatus
