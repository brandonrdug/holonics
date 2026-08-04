#pragma once

#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/return_conditioning_return.hpp>

namespace holonics::apparatus {

enum class return_conditioning_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  conditioning_refused
};

struct return_conditioning_mount final {
  organ::theorem_production_foundation foundation{};
  event::theorem_production_rest_record inherited{};
  receiver::dependent_theorem_question question{};
};

struct return_conditioning_executor_receipt final {
  return_conditioning_executor_status state{return_conditioning_executor_status::invalid_aperture};
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
    return state == return_conditioning_executor_status::returned;
  }
};

[[nodiscard]] return_conditioning_executor_receipt execute_return_conditioning(
    const return_conditioning_mount& mount,
    event::return_conditioning_observation& observation,
    event::theorem_production_rest_record& handoff,
    event::dependent_theorem_setup& setup) noexcept;

}  // namespace holonics::apparatus
