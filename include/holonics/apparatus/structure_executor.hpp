#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/structure/complex_schema.hpp>

namespace holonics::apparatus {

enum class structure_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct structure_batch final {
  const structure::structure_case* inputs{};
  structure::structure_output* outputs{};
  std::size_t count{};
};

struct structure_executor_receipt final {
  structure_executor_status state{structure_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_structure_bytes{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == structure_executor_status::returned;
  }
};

[[nodiscard]] structure_executor_receipt execute_structure_deeds(structure_batch batch) noexcept;

}  // namespace holonics::apparatus
