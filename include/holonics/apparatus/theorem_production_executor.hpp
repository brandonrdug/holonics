#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/theorem_production_return.hpp>
#include <holonics/receiver/theorem_production_question.hpp>

namespace holonics::apparatus {

enum class theorem_production_executor_status : std::uint8_t {
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

struct theorem_production_mount final {
  organ::theorem_production_foundation foundation{};
  receiver::theorem_production_question question{};
  receiver::dependent_theorem_question held_probe{};
  body::rest_region regions[body::live_region_capacity]{};
  std::uint64_t body_seed{};
  std::uint64_t mathematical_admitted_tally{};
  std::uint64_t codec_admitted_tally{};
};

struct theorem_production_executor_receipt final {
  theorem_production_executor_status state{theorem_production_executor_status::invalid_aperture};
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
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == theorem_production_executor_status::returned;
  }
};

[[nodiscard]] theorem_production_executor_receipt execute_theorem_production(
    const theorem_production_mount& mount,
    const lean_process_configuration& process,
    event::theorem_production_observation& observation,
    event::theorem_production_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
