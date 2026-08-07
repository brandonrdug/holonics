#include <cstddef>
#include <cstdint>

#include <cuda_runtime.h>

#include <holonics/apparatus/source_topology_resident.hpp>
#include <holonics/receiver/projective_transition.hpp>

namespace holonics::apparatus {
namespace {

__device__ std::uint64_t fold_identity(std::uint64_t identity, std::uint8_t face) {
  std::uint64_t fold = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  std::uint64_t values[2]{identity, face};
  for (std::size_t field = 0; field < 2; ++field) {
    for (std::size_t octet = 0; octet < 8; ++octet) {
      fold ^= values[field] & 255U;
      fold *= prime;
      values[field] >>= 8U;
    }
  }
  return fold;
}

__device__ void inspect_preimage(
    const structure::resident_marked_population& population,
    const receiver::resident_projection_chart& chart,
    std::uint8_t face,
    std::uint64_t requested_occurrence,
    receiver::preimage_receipt& receipt) {
  receipt.face = face;
  receipt.projection_words_touched = static_cast<std::uint16_t>(chart.word_count());
  for (std::size_t word_slot = 0; word_slot < chart.word_count(); ++word_slot) {
    const std::uint64_t word = chart.word(face, word_slot);
    for (std::size_t bit = 0; bit < 64; ++bit) {
      const std::size_t occurrence_slot = word_slot * 64U + bit;
      if (occurrence_slot >= chart.occurrence_count()) {
        break;
      }
      if ((word & (std::uint64_t{1} << bit)) == 0) {
        continue;
      }
      const std::uint64_t identity = population.occurrence(occurrence_slot).occurrence().serial().value();
      receipt.occurrence_fold ^= fold_identity(identity, face);
      if (identity == requested_occurrence) {
        receipt.selected_occurrence = identity;
      }
      ++receipt.occurrences_touched;
    }
  }
  if (receipt.occurrences_touched == 0) {
    receipt.state = receiver::navigation_status::empty_preimage;
  } else if (receipt.selected_occurrence == 0) {
    receipt.state = receiver::navigation_status::requested_occurrence_outside_preimage;
  }
}

__device__ void inspect_support(
    const structure::resident_marked_population& population,
    std::size_t selected_slot,
    receiver::local_support_receipt& receipt) {
  const auto& selected = population.occurrence(selected_slot);
  const auto& source = population.source(selected.source_slot());
  const std::size_t local = selected.local_coordinate();
  const std::size_t begin = local > 2 ? local - 2 : 0;
  const std::size_t proposed_end = local + 3;
  const std::size_t end = proposed_end < source.occurrence_count()
      ? proposed_end : source.occurrence_count();
  receipt.occurrence_count = static_cast<std::uint16_t>(end - begin);
  receipt.relation_count = static_cast<std::uint16_t>(end - begin - 1);
  receipt.source_occurrence_count = source.occurrence_count();
  receipt.source_relation_count = static_cast<std::uint16_t>(source.occurrence_count() - 1);
  for (std::size_t slot = begin; slot < end; ++slot) {
    const std::size_t output_slot = slot - begin;
    receipt.occurrence_identities[output_slot] =
        population.occurrence(source.occurrence_begin() + slot).occurrence().serial().value();
    receipt.payloads[output_slot] = static_cast<std::uint8_t>(
        population.occurrence(source.occurrence_begin() + slot).payload().value());
  }
}

__global__ void navigate(
    const structure::resident_marked_population* populations,
    const receiver::resident_projection_chart* charts,
    const source_mount_accumulator* accumulators,
    source_topology_output* output,
    std::uint8_t query_face,
    std::uint8_t obstruction_face,
    std::uint64_t query_occurrence) {
  const std::size_t variant_slot = threadIdx.x;
  if (blockIdx.x != 0 || variant_slot >= codec::source_variant_capacity) {
    return;
  }
  const auto& population = populations[variant_slot];
  const auto& chart = charts[variant_slot];
  const auto& accumulator = accumulators[variant_slot];
  auto& returned = output->variants[variant_slot];
  returned.population.occurrence_fold = exact::word{accumulator.occurrence_fold};
  returned.population.relation_fold = exact::word{accumulator.relation_fold};
  returned.transduction.pair_fold = accumulator.pair_fold;
  if (accumulator.malformed != 0) {
    returned.population.state = structure::marked_population_status::malformed;
    returned.transduction.state = codec::transduction_status::malformed_cut;
  } else if (accumulator.occurrences_seen != returned.population.occurrence_count ||
      accumulator.relations_seen != returned.population.relation_count) {
    returned.population.state = structure::marked_population_status::malformed;
    returned.transduction.state = codec::transduction_status::incomplete_cover;
  }
  auto& navigation = returned.navigation;
  inspect_preimage(population, chart, query_face, query_occurrence, navigation.preimage);
  inspect_preimage(population, chart, obstruction_face, query_occurrence, navigation.obstruction);
  if (navigation.preimage.state == receiver::navigation_status::exact &&
      navigation.preimage.selected_occurrence != 0) {
    const std::size_t selected_slot = static_cast<std::size_t>(
        navigation.preimage.selected_occurrence - population.occurrence_id(0).serial().value());
    const auto& selected = population.occurrence(selected_slot);
    inspect_support(population, selected_slot, navigation.support);
    const auto transition = receiver::transition_face(
        selected.local_coordinate(),
        population.source(selected.source_slot()).occurrence_count(), query_face);
    navigation.transition.invertible = transition.invertible;
    navigation.transition.determinant_negative = transition.determinant.negative();
    navigation.transition.determinant_magnitude = transition.determinant.magnitude().limb(0);
    navigation.transition.sequence_first = transition.sequence.first.limb(0);
    navigation.transition.sequence_second = transition.sequence.second.limb(0);
    navigation.transition.projected_first = transition.projected.first.limb(0);
    navigation.transition.projected_second = transition.projected.second.limb(0);
    navigation.overlap.occurrence = navigation.preimage.selected_occurrence;
    navigation.overlap.projection_chart = chart.projection_serial();
    navigation.overlap.sequence_chart = chart.sequence_serial();
    navigation.overlap.same_source_occurrence = true;
  }
  navigation.source_bytes_visible_to_query = 0;
  __syncthreads();
  if (variant_slot == 0) {
    output->source_mismatches = accumulator.source_mismatches;
    output->occurrence_mismatches = accumulator.occurrence_mismatches;
    output->relation_mismatches = accumulator.relation_mismatches;
    output->direct_oracle_mismatches = accumulator.direct_oracle_mismatches;
    output->semantic_occurrence_invariant = accumulator.source_mismatches == 0 &&
        accumulator.occurrence_mismatches == 0 && accumulator.direct_oracle_mismatches == 0;
    output->semantic_relation_invariant = accumulator.relation_mismatches == 0 &&
        accumulator.direct_oracle_mismatches == 0;
    output->detached_query_returned = true;
    for (std::size_t slot = 1; slot < codec::source_variant_capacity; ++slot) {
      output->detached_query_returned = output->detached_query_returned &&
          output->variants[slot].navigation.source_bytes_visible_to_query == 0;
    }
  }
}

}  // namespace

cudaError_t launch_detached_navigation(
    const structure::resident_marked_population* populations,
    const receiver::resident_projection_chart* charts,
    const source_mount_accumulator* accumulators,
    source_topology_output* output,
    std::uint8_t query_face,
    std::uint8_t obstruction_face,
    std::uint64_t query_occurrence) noexcept {
  navigate<<<1, codec::source_variant_capacity>>>(
      populations, charts, accumulators, output, query_face, obstruction_face, query_occurrence);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
