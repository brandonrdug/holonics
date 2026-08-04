#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_toric_cycle_return.hpp>

namespace holonics::apparatus {

struct toric_cycle_mount final {
  organ::toric_cycle_foundation foundation{};
  organ::toric_cycle_question question{};
  event::cm_incidence_rest_record inherited{};
};

enum class toric_executor_status : std::uint8_t {
  returned,
  invalid_mount,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  derivation_refused,
  formation_refused,
  process_refused,
  return_refused,
  rest_refused
};

struct toric_executor_receipt final {
  toric_executor_status state{toric_executor_status::invalid_mount};
  lean_process_receipt process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word semantic_threads{};
  exact::word host_semantic_events{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == toric_executor_status::returned;
  }
};

[[nodiscard]] toric_executor_receipt execute_toric_cycle(
    const toric_cycle_mount& mount, const lean_process_configuration& process,
    event::toric_cycle_observation& observation,
    event::toric_cycle_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
