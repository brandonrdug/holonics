#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_cm_incidence_return.hpp>

namespace holonics::apparatus {

struct cm_incidence_mount final {
  organ::cm_incidence_foundation foundation{};
  organ::cm_incidence_question question{};
  event::blind_reconstruction_rest_record inherited{};
};

enum class cm_executor_status : std::uint8_t {
  returned,
  invalid_mount,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  arithmetic_refused,
  incidence_refused,
  characteristic_refused,
  formation_refused,
  process_refused,
  return_refused,
  rest_refused
};

struct cm_executor_receipt final {
  cm_executor_status state{cm_executor_status::invalid_mount};
  lean_process_receipt process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word arithmetic_threads{};
  exact::word characteristic_threads{};
  exact::word host_semantic_events{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == cm_executor_status::returned;
  }
};

[[nodiscard]] cm_executor_receipt execute_cm_incidence(
    const cm_incidence_mount& mount, const lean_process_configuration& process,
    event::cm_incidence_observation& observation,
    event::cm_incidence_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
