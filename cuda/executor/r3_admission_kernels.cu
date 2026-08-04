#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/source_topology_resident.hpp>

namespace holonics::apparatus {
namespace {

[[nodiscard]] __device__ std::size_t source_for_occurrence(
    const codec::encoded_source_environment& environment,
    std::size_t occurrence_slot) {
  std::size_t source_slot = 0;
  while (source_slot + 1 < environment.source_count && occurrence_slot >=
      static_cast<std::size_t>(environment.sources[source_slot].byte_begin) +
          environment.sources[source_slot].byte_count) {
    ++source_slot;
  }
  return source_slot;
}

[[nodiscard]] __device__ std::size_t source_for_relation(
    const codec::encoded_source_environment& environment,
    std::size_t relation_slot) {
  std::size_t source_slot = 0;
  while (source_slot + 1 < environment.source_count && relation_slot >=
      static_cast<std::size_t>(environment.sources[source_slot].relation_begin) +
          environment.sources[source_slot].byte_count - 1U) {
    ++source_slot;
  }
  return source_slot;
}

__global__ void compare_resident_variants(
    const codec::encoded_source_environment* environment,
    const structure::resident_marked_population* populations,
    source_mount_accumulator* accumulators) {
  const std::size_t slot = static_cast<std::size_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  auto& receipt = accumulators[0];
  if (slot < environment->source_count) {
    for (std::size_t variant = 1; variant < codec::source_variant_capacity; ++variant) {
      if (!(populations[variant].source(slot) == populations[0].source(slot))) {
        atomicAdd(&receipt.source_mismatches, 1U);
      }
    }
  }
  if (slot < environment->byte_count) {
    const auto& actual = populations[0].occurrence(slot);
    for (std::size_t variant = 1; variant < codec::source_variant_capacity; ++variant) {
      if (!(populations[variant].occurrence(slot) == actual)) {
        atomicAdd(&receipt.occurrence_mismatches, 1U);
      }
    }
    const std::size_t source_slot = source_for_occurrence(*environment, slot);
    const auto source = environment->sources[source_slot];
    const std::size_t local = slot - source.byte_begin;
    const std::uint16_t incoming = local == 0 ? structure::no_marked_slot
        : static_cast<std::uint16_t>(source.relation_begin + local - 1U);
    const std::uint16_t outgoing = local + 1U == source.byte_count
        ? structure::no_marked_slot
        : static_cast<std::uint16_t>(source.relation_begin + local);
    const structure::marked_occurrence expected{
        populations[0].occurrence_id(slot), populations[0].source_id(source_slot),
        populations[0].cut_id(source.cut_begin + local),
        populations[0].cut_id(source.cut_begin + local + 1U),
        populations[0].lineage_id(slot), exact::word{environment->bytes[slot]},
        static_cast<std::uint16_t>(source_slot), static_cast<std::uint16_t>(local),
        incoming, outgoing};
    if (!(actual == expected)) {
      atomicAdd(&receipt.direct_oracle_mismatches, 1U);
    }
  }
  if (slot < environment->relation_count) {
    const auto& actual = populations[0].relation(slot);
    for (std::size_t variant = 1; variant < codec::source_variant_capacity; ++variant) {
      if (!(populations[variant].relation(slot) == actual)) {
        atomicAdd(&receipt.relation_mismatches, 1U);
      }
    }
    const std::size_t source_slot = source_for_relation(*environment, slot);
    const auto source = environment->sources[source_slot];
    const std::size_t local = slot - source.relation_begin;
    const std::size_t occurrence_slot = source.byte_begin + local;
    const std::uint64_t label = static_cast<std::uint64_t>(environment->bytes[occurrence_slot]) *
        256U + environment->bytes[occurrence_slot + 1U];
    const structure::marked_relation expected{
        populations[0].event_id(slot), populations[0].port_id(slot),
        populations[0].lineage_id(environment->byte_count + slot),
        static_cast<std::uint16_t>(occurrence_slot),
        static_cast<std::uint16_t>(occurrence_slot + 1U), exact::word{label}};
    if (!(actual == expected)) {
      atomicAdd(&receipt.direct_oracle_mismatches, 1U);
    }
  }
}

}  // namespace

cudaError_t launch_source_admission(
    const codec::encoded_source_environment* environment,
    const structure::resident_marked_population* populations,
    source_mount_accumulator* accumulators) noexcept {
  constexpr unsigned block_width = 128;
  constexpr unsigned grid_width = static_cast<unsigned>(
      (structure::marked_occurrence_capacity + block_width - 1U) / block_width);
  compare_resident_variants<<<grid_width, block_width>>>(environment, populations, accumulators);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
