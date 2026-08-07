#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_intrinsic_hypergeometry_rest.hpp>
#include <holonics/event/resident_intrinsic_hypergeometry_return.hpp>

namespace holonics::apparatus {

struct intrinsic_hypergeometry_mount final {
  organ::intrinsic_hypergeometry_foundation foundation{};
  organ::intrinsic_hypergeometry_foundation changed_foundation{};
  organ::intrinsic_hypergeometry_question question{};
  event::causal_linear_rest_record inherited{};
};

enum class intrinsic_hypergeometry_executor_status : std::uint8_t {
  returned, invalid_mount, device_unavailable, allocation_refused, transfer_refused,
  derivation_refused, formation_refused, process_refused, return_refused, rest_refused
};

struct intrinsic_hypergeometry_executor_receipt final {
  intrinsic_hypergeometry_executor_status state{
      intrinsic_hypergeometry_executor_status::invalid_mount};
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
    return state == intrinsic_hypergeometry_executor_status::returned;
  }
};

[[nodiscard]] intrinsic_hypergeometry_executor_receipt execute_intrinsic_hypergeometry(
    const intrinsic_hypergeometry_mount& mount,
    const lean_process_configuration& process,
    event::intrinsic_hypergeometry_observation& observation,
    event::intrinsic_hypergeometry_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
