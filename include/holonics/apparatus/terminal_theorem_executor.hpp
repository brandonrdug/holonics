#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/terminal_theorem_return.hpp>

namespace holonics::apparatus {

enum class terminal_theorem_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  generation_refused,
  process_refused,
  return_refused,
  rest_refused
};

struct terminal_theorem_mount final {
  organ::theorem_production_foundation foundation{};
  event::theorem_production_rest_record inherited{};
  event::dependent_theorem_setup setup{};
};

struct terminal_theorem_executor_receipt final {
  terminal_theorem_executor_status state{terminal_theorem_executor_status::invalid_aperture};
  lean_process_receipt process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word host_semantic_events{};
  exact::word engine_source_reads{};
  exact::word exterior_retrieval_calls{};
  exact::word developmental_source_bytes{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == terminal_theorem_executor_status::returned;
  }
};

[[nodiscard]] terminal_theorem_executor_receipt execute_terminal_theorem(
    const terminal_theorem_mount& mount,
    const lean_process_configuration& process,
    event::terminal_theorem_observation& observation,
    event::terminal_theorem_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
