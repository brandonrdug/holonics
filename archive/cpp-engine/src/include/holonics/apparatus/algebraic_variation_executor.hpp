#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_algebraic_variation_rest.hpp>
#include <holonics/event/resident_algebraic_variation_return.hpp>

namespace holonics::apparatus {

struct algebraic_variation_mount final {
  organ::algebraic_variation_foundation foundation{};
  organ::algebraic_variation_question question{};
  event::toric_cycle_rest_record inherited{};
};

enum class variation_executor_status : std::uint8_t {
  returned, invalid_mount, device_unavailable, allocation_refused, transfer_refused,
  derivation_refused, formation_refused, process_refused, return_refused, rest_refused
};

struct variation_executor_receipt final {
  variation_executor_status state{variation_executor_status::invalid_mount};
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
    return state == variation_executor_status::returned;
  }
};

[[nodiscard]] variation_executor_receipt execute_algebraic_variation(
    const algebraic_variation_mount& mount, const lean_process_configuration& process,
    event::algebraic_variation_observation& observation,
    event::algebraic_variation_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
