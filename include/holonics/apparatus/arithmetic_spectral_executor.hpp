#pragma once

#include <holonics/apparatus/arithmetic_spectral_store_adapter.hpp>
#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_arithmetic_spectral_mount.hpp>
#include <holonics/event/resident_arithmetic_spectral_rest.hpp>
#include <holonics/event/resident_arithmetic_spectral_return.hpp>

namespace holonics::apparatus {

struct arithmetic_spectral_mount final {
  organ::arithmetic_spectral_foundation foundation{};
  organ::arithmetic_spectral_question question{};
  event::hodge_realization_rest_record inherited{};
};

enum class arithmetic_executor_status : std::uint8_t {
  returned, invalid_mount, device_unavailable, allocation_refused, transfer_refused,
  derivation_refused, formation_refused, process_refused, return_refused, rest_refused
};

struct arithmetic_executor_receipt final {
  arithmetic_executor_status state{arithmetic_executor_status::invalid_mount};
  lean_process_receipt process{}; current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{}; exact::word bytes_to_device{};
  exact::word bytes_from_device{}; exact::word resident_bytes{}; exact::word kernel_launches{};
  exact::word launched_threads{}; exact::word semantic_threads{}; exact::word host_semantic_events{};
  std::uint32_t device_major{}; std::uint32_t device_minor{};
  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == arithmetic_executor_status::returned;
  }
};

[[nodiscard]] arithmetic_executor_receipt execute_arithmetic_spectral(
    const arithmetic_spectral_mount& mount, const lean_process_configuration& process,
    event::arithmetic_spectral_observation& observation,
    organ::arithmetic_spectral_workspace& workspace,
    event::arithmetic_spectral_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
