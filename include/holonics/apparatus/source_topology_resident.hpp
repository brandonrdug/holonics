#pragma once

#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/source_topology_executor.hpp>
#include <holonics/receiver/projection_chart.hpp>
#include <holonics/structure/resident_marked_population.hpp>

namespace holonics::apparatus {

struct chunk_boundary_summary final {
  std::uint16_t source_slot{};
  std::uint16_t local_begin{};
  std::uint16_t byte_count{};
  std::uint16_t next_chunk{codec::no_chunk_slot};
  std::uint8_t first{};
  std::uint8_t last{};
};

struct source_mount_accumulator final {
  std::uint64_t occurrence_fold{};
  std::uint64_t relation_fold{};
  std::uint64_t pair_fold{};
  std::uint32_t occurrences_seen{};
  std::uint32_t relations_seen{};
  std::uint32_t malformed{};
  std::uint32_t source_mismatches{};
  std::uint32_t occurrence_mismatches{};
  std::uint32_t relation_mismatches{};
  std::uint32_t direct_oracle_mismatches{};
};

[[nodiscard]] cudaError_t launch_source_foundation(
    const codec::encoded_source_environment* environment,
    structure::resident_marked_population* populations,
    receiver::resident_projection_chart* charts,
    chunk_boundary_summary* summaries,
    source_mount_accumulator* accumulators,
    source_topology_output* output) noexcept;

[[nodiscard]] cudaError_t launch_source_admission(
    const codec::encoded_source_environment* environment,
    const structure::resident_marked_population* populations,
    source_mount_accumulator* accumulators) noexcept;

[[nodiscard]] cudaError_t launch_detached_navigation(
    const structure::resident_marked_population* populations,
    const receiver::resident_projection_chart* charts,
    const source_mount_accumulator* accumulators,
    source_topology_output* output,
    std::uint8_t query_face,
    std::uint8_t obstruction_face,
    std::uint64_t query_occurrence) noexcept;

}  // namespace holonics::apparatus
