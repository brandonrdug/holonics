#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_causal_linear_rest.hpp>
#include <holonics/event/resident_causal_linear_return.hpp>

namespace holonics::apparatus {

struct causal_linear_mount final {
  organ::causal_linear_foundation foundation{};
  organ::causal_linear_question question{};
  event::algebraic_variation_rest_record inherited{};
};

enum class causal_linear_executor_status : std::uint8_t {
  returned, invalid_mount, device_unavailable, allocation_refused, transfer_refused,
  derivation_refused, formation_refused, process_refused, return_refused, rest_refused
};

struct causal_linear_executor_receipt final {
  causal_linear_executor_status state{causal_linear_executor_status::invalid_mount};
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
    return state == causal_linear_executor_status::returned;
  }
};

[[nodiscard]] causal_linear_executor_receipt execute_causal_linear(
    const causal_linear_mount& mount, const lean_process_configuration& process,
    event::causal_linear_observation& observation,
    event::causal_linear_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
