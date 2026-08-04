#include <cstddef>
#include <cstdint>
#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/source_topology_resident.hpp>
#include <holonics/receiver/projective_transition.hpp>

namespace holonics::apparatus {
namespace {

__device__ std::uint64_t record_hash(
    std::uint64_t first,
    std::uint64_t second,
    std::uint64_t third,
    std::uint64_t fourth) {
  std::uint64_t value = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  const std::uint64_t fields[4]{first, second, third, fourth};
  for (std::size_t field = 0; field < 4; ++field) {
    std::uint64_t current = fields[field];
    for (std::size_t octet = 0; octet < 8; ++octet) {
      value ^= current & 255U;
      value *= prime;
      current >>= 8U;
    }
  }
  return value;
}

__device__ void fold_xor(std::uint64_t* destination, std::uint64_t value) {
  atomicXor(reinterpret_cast<unsigned long long*>(destination),
      static_cast<unsigned long long>(value));
}

__global__ void initialize_mounts(
    const codec::encoded_source_environment* environment,
    structure::resident_marked_population* populations,
    receiver::resident_projection_chart* charts,
    source_topology_output* output) {
  const std::size_t variant_slot = threadIdx.x;
  if (blockIdx.x != 0 || variant_slot >= codec::source_variant_capacity) {
    return;
  }
  const auto variant = environment->variants[variant_slot];
  auto* population = ::new (static_cast<void*>(populations + variant_slot))
      structure::resident_marked_population{variant.owner_seed, environment->source_count,
          environment->byte_count, environment->relation_count};
  auto* chart = ::new (static_cast<void*>(charts + variant_slot))
      receiver::resident_projection_chart{variant.owner_seed + 6'000'000U,
          environment->byte_count};
  auto& returned = output->variants[variant_slot];
  returned.population.state = population->admitted() && chart->admitted()
      ? structure::marked_population_status::exact
      : structure::marked_population_status::capacity_refused;
  returned.population.source_count = environment->source_count;
  returned.population.occurrence_count = environment->byte_count;
  returned.population.relation_count = environment->relation_count;
  returned.transduction.chunks = variant.chunk_count;
  returned.transduction.boundary_summaries = variant.chunk_count;
  returned.transduction.cross_cut_relations =
      static_cast<std::uint16_t>(variant.chunk_count - environment->source_count);
  returned.transduction.local_relations = static_cast<std::uint16_t>(
      environment->relation_count - returned.transduction.cross_cut_relations);
  returned.transduction.source_bytes_visible = environment->byte_count;
  for (std::size_t source_slot = 0; source_slot < environment->source_count; ++source_slot) {
    const auto source = environment->sources[source_slot];
    population->construct_source(source_slot, population->source_id(source_slot),
        source.byte_begin, source.byte_count, source.relation_begin, source.cut_begin);
  }
}

__global__ void transduce_chunks(
    const codec::encoded_source_environment* environment,
    structure::resident_marked_population* populations,
    receiver::resident_projection_chart* charts,
    chunk_boundary_summary* summaries,
    source_mount_accumulator* accumulators) {
  const std::size_t chunk_slot = static_cast<std::size_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (chunk_slot >= environment->chunk_count) {
    return;
  }
  std::size_t variant_slot = 0;
  while (variant_slot + 1 < codec::source_variant_capacity && chunk_slot >=
      static_cast<std::size_t>(environment->variants[variant_slot].chunk_begin) +
          environment->variants[variant_slot].chunk_count) {
    ++variant_slot;
  }
  const auto chunk = environment->chunks[chunk_slot];
  const auto source = environment->sources[chunk.source_slot];
  auto& population = populations[variant_slot];
  auto& chart = charts[variant_slot];
  auto& accumulator = accumulators[variant_slot];
  summaries[chunk_slot] = chunk_boundary_summary{chunk.source_slot, chunk.local_begin,
      chunk.byte_count, chunk.next_chunk,
      environment->bytes[source.byte_begin + chunk.local_begin],
      environment->bytes[source.byte_begin + chunk.local_begin + chunk.byte_count - 1]};
  for (std::size_t local = chunk.local_begin;
       local < static_cast<std::size_t>(chunk.local_begin) + chunk.byte_count; ++local) {
    const std::size_t occurrence_slot = source.byte_begin + local;
    const std::uint8_t payload = environment->bytes[occurrence_slot];
    const std::uint16_t incoming = local == 0
        ? structure::no_marked_slot
        : static_cast<std::uint16_t>(source.relation_begin + local - 1);
    const std::uint16_t outgoing = local + 1 == source.byte_count
        ? structure::no_marked_slot
        : static_cast<std::uint16_t>(source.relation_begin + local);
    population.construct_occurrence(occurrence_slot, population.occurrence_id(occurrence_slot),
        population.source_id(chunk.source_slot), population.cut_id(source.cut_begin + local),
        population.cut_id(source.cut_begin + local + 1), population.lineage_id(occurrence_slot),
        exact::word{payload}, chunk.source_slot, static_cast<std::uint16_t>(local), incoming, outgoing);
    atomicOr(reinterpret_cast<unsigned long long*>(chart.word_address(payload, occurrence_slot / 64U)),
        static_cast<unsigned long long>(std::uint64_t{1} << (occurrence_slot % 64U)));
    fold_xor(&accumulator.occurrence_fold,
        record_hash(population.occurrence_id(occurrence_slot).serial().value(),
            population.source_id(chunk.source_slot).serial().value(), local, payload));
    atomicAdd(&accumulator.occurrences_seen, 1U);
    if (local + 1 < static_cast<std::size_t>(chunk.local_begin) + chunk.byte_count) {
      const std::size_t relation_slot = source.relation_begin + local;
      const std::uint64_t label = static_cast<std::uint64_t>(payload) * 256U +
          environment->bytes[occurrence_slot + 1];
      population.construct_relation(relation_slot, population.event_id(relation_slot),
          population.port_id(relation_slot),
          population.lineage_id(environment->byte_count + relation_slot),
          static_cast<std::uint16_t>(occurrence_slot),
          static_cast<std::uint16_t>(occurrence_slot + 1), exact::word{label});
      const std::uint64_t relation_hash = record_hash(relation_slot, occurrence_slot,
          occurrence_slot + 1, label);
      fold_xor(&accumulator.relation_fold, relation_hash);
      fold_xor(&accumulator.pair_fold, relation_hash);
      atomicAdd(&accumulator.relations_seen, 1U);
    }
  }
}

__global__ void join_boundaries(
    const codec::encoded_source_environment* environment,
    structure::resident_marked_population* populations,
    const chunk_boundary_summary* summaries,
    source_mount_accumulator* accumulators) {
  const std::size_t chunk_slot = static_cast<std::size_t>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (chunk_slot >= environment->chunk_count || summaries[chunk_slot].next_chunk == codec::no_chunk_slot) {
    return;
  }
  std::size_t variant_slot = 0;
  while (variant_slot + 1 < codec::source_variant_capacity && chunk_slot >=
      static_cast<std::size_t>(environment->variants[variant_slot].chunk_begin) +
          environment->variants[variant_slot].chunk_count) {
    ++variant_slot;
  }
  const auto current = summaries[chunk_slot];
  const auto next = summaries[current.next_chunk];
  auto& accumulator = accumulators[variant_slot];
  if (current.source_slot != next.source_slot ||
      current.local_begin + current.byte_count != next.local_begin) {
    atomicAdd(&accumulator.malformed, 1U);
    return;
  }
  const auto source = environment->sources[current.source_slot];
  const std::size_t local = current.local_begin + current.byte_count - 1;
  const std::size_t occurrence_slot = source.byte_begin + local;
  const std::size_t relation_slot = source.relation_begin + local;
  const std::uint64_t label = static_cast<std::uint64_t>(current.last) * 256U + next.first;
  auto& population = populations[variant_slot];
  population.construct_relation(relation_slot, population.event_id(relation_slot),
      population.port_id(relation_slot),
      population.lineage_id(environment->byte_count + relation_slot),
      static_cast<std::uint16_t>(occurrence_slot),
      static_cast<std::uint16_t>(occurrence_slot + 1), exact::word{label});
  const std::uint64_t relation_hash = record_hash(
      relation_slot, occurrence_slot, occurrence_slot + 1, label);
  fold_xor(&accumulator.relation_fold, relation_hash);
  fold_xor(&accumulator.pair_fold, relation_hash);
  atomicAdd(&accumulator.relations_seen, 1U);
}

}  // namespace

cudaError_t launch_source_foundation(
    const codec::encoded_source_environment* environment,
    structure::resident_marked_population* populations,
    receiver::resident_projection_chart* charts,
    chunk_boundary_summary* summaries,
    source_mount_accumulator* accumulators,
    source_topology_output* output) noexcept {
  initialize_mounts<<<1, codec::source_variant_capacity>>>(environment, populations, charts, output);
  constexpr unsigned block_width = 128;
  constexpr unsigned grid_width = static_cast<unsigned>(
      (codec::source_chunk_capacity + block_width - 1U) / block_width);
  transduce_chunks<<<grid_width, block_width>>>(environment, populations, charts, summaries, accumulators);
  join_boundaries<<<grid_width, block_width>>>(environment, populations, summaries, accumulators);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
