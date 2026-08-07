#pragma once

#include <holonics/apparatus/hodge_realization_store_adapter.hpp>
#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_hodge_realization_mount.hpp>
#include <holonics/event/resident_hodge_realization_rest.hpp>
#include <holonics/event/resident_hodge_realization_return.hpp>

namespace holonics::apparatus {

struct hodge_realization_mount final {
  organ::hodge_realization_foundation foundation{};
  organ::hodge_realization_question question{};
  event::expression_geometry_rest_record inherited{};
};

enum class hodge_executor_status : std::uint8_t {
  returned, invalid_mount, device_unavailable, allocation_refused, transfer_refused,
  derivation_refused, formation_refused, process_refused, return_refused, rest_refused
};

struct hodge_executor_receipt final {
  hodge_executor_status state{hodge_executor_status::invalid_mount};
  lean_process_receipt process{}; current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{}; exact::word bytes_to_device{};
  exact::word bytes_from_device{}; exact::word resident_bytes{}; exact::word kernel_launches{};
  exact::word launched_threads{}; exact::word semantic_threads{}; exact::word host_semantic_events{};
  std::uint32_t device_major{}; std::uint32_t device_minor{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == hodge_executor_status::returned;
  }
};

[[nodiscard]] hodge_executor_receipt execute_hodge_realization(
    const hodge_realization_mount& mount, const lean_process_configuration& process,
    event::hodge_realization_observation& observation,
    event::hodge_realization_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
