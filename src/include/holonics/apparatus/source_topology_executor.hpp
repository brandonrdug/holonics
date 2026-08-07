#pragma once

#include <cstdint>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/codec/source_environment.hpp>
#include <holonics/codec/source_schema.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/receiver/navigation_receipt.hpp>
#include <holonics/structure/marked_population_receipt.hpp>

namespace holonics::apparatus {

enum class source_topology_executor_status : std::uint8_t {
  returned,
  invalid_aperture,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  launch_refused,
  synchronization_refused
};

struct source_variant_output final {
  structure::marked_population_receipt population{};
  codec::transduction_receipt transduction{};
  receiver::navigation_receipt navigation{};
};

struct source_topology_output final {
  source_variant_output variants[codec::source_variant_capacity]{};
  bool semantic_occurrence_invariant{};
  bool semantic_relation_invariant{};
  bool detached_query_returned{};
  std::uint32_t source_mismatches{};
  std::uint32_t occurrence_mismatches{};
  std::uint32_t relation_mismatches{};
  std::uint32_t direct_oracle_mismatches{};
};

struct source_topology_executor_receipt final {
  source_topology_executor_status state{source_topology_executor_status::invalid_aperture};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_structure_bytes{};
  exact::word resident_chart_bytes{};
  exact::word launched_threads{};
  exact::word kernel_launches{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == source_topology_executor_status::returned;
  }
};

[[nodiscard]] source_topology_executor_receipt execute_source_topology(
    codec::source_environment&& environment,
    source_topology_output& output) noexcept;

}  // namespace holonics::apparatus
