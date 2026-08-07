#include "r3_verify.hpp"

#include <cstddef>
#include <cstdint>

namespace holonics::tests {
namespace {

[[nodiscard]] std::uint64_t record_hash(
    std::uint64_t first,
    std::uint64_t second,
    std::uint64_t third,
    std::uint64_t fourth) noexcept {
  std::uint64_t value = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  std::uint64_t fields[4]{first, second, third, fourth};
  for (std::size_t field = 0; field < 4; ++field) {
    for (std::size_t octet = 0; octet < 8; ++octet) {
      value ^= fields[field] & 255U;
      value *= prime;
      fields[field] >>= 8U;
    }
  }
  return value;
}

[[nodiscard]] std::uint64_t preimage_hash(
    std::uint64_t identity,
    std::uint8_t face) noexcept {
  std::uint64_t value = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  std::uint64_t fields[2]{identity, face};
  for (std::size_t field = 0; field < 2; ++field) {
    for (std::size_t octet = 0; octet < 8; ++octet) {
      value ^= fields[field] & 255U;
      value *= prime;
      fields[field] >>= 8U;
    }
  }
  return value;
}

void fill_navigation(
    const codec::encoded_source_environment& encoded,
    const codec::encoded_mount_variant& variant,
    receiver::navigation_receipt& navigation) noexcept {
  const std::uint64_t occurrence_seed = variant.owner_seed;
  navigation.preimage.face = encoded.query_face;
  navigation.preimage.projection_words_touched = static_cast<std::uint16_t>(
      (encoded.byte_count + 63U) / 64U);
  std::size_t selected = encoded.byte_count;
  for (std::size_t slot = 0; slot < encoded.byte_count; ++slot) {
    if (encoded.bytes[slot] == encoded.query_face) {
      navigation.preimage.occurrence_fold ^=
          preimage_hash(occurrence_seed + slot, encoded.query_face);
      if (occurrence_seed + slot == encoded.query_occurrence) {
        selected = slot;
        navigation.preimage.selected_occurrence = encoded.query_occurrence;
      }
      ++navigation.preimage.occurrences_touched;
    }
  }
  navigation.obstruction.face = encoded.obstruction_face;
  navigation.obstruction.projection_words_touched = navigation.preimage.projection_words_touched;
  for (std::size_t slot = 0; slot < encoded.byte_count; ++slot) {
    if (encoded.bytes[slot] == encoded.obstruction_face) {
      navigation.obstruction.occurrence_fold ^=
          preimage_hash(occurrence_seed + slot, encoded.obstruction_face);
      ++navigation.obstruction.occurrences_touched;
    }
  }
  if (navigation.obstruction.occurrences_touched == 0) {
    navigation.obstruction.state = receiver::navigation_status::empty_preimage;
  }
  if (navigation.preimage.occurrences_touched != 0 && selected == encoded.byte_count) {
    navigation.preimage.state = receiver::navigation_status::requested_occurrence_outside_preimage;
  }
  if (selected == encoded.byte_count) {
    if (navigation.preimage.occurrences_touched == 0) {
      navigation.preimage.state = receiver::navigation_status::empty_preimage;
    }
    return;
  }
  std::size_t source_slot = 0;
  while (selected >= static_cast<std::size_t>(encoded.sources[source_slot].byte_begin) +
      encoded.sources[source_slot].byte_count) {
    ++source_slot;
  }
  const auto source = encoded.sources[source_slot];
  const std::size_t local = selected - source.byte_begin;
  const std::size_t begin = local > 2 ? local - 2 : 0;
  const std::size_t proposed_end = local + 3;
  const std::size_t end = proposed_end < source.byte_count ? proposed_end : source.byte_count;
  navigation.support.occurrence_count = static_cast<std::uint16_t>(end - begin);
  navigation.support.relation_count = static_cast<std::uint16_t>(end - begin - 1);
  navigation.support.source_occurrence_count = source.byte_count;
  navigation.support.source_relation_count = static_cast<std::uint16_t>(source.byte_count - 1);
  for (std::size_t slot = begin; slot < end; ++slot) {
    navigation.support.occurrence_identities[slot - begin] =
        occurrence_seed + source.byte_begin + slot;
    navigation.support.payloads[slot - begin] = encoded.bytes[source.byte_begin + slot];
  }
  const std::uint64_t sequence_first = local + 1;
  const std::uint64_t sequence_second = source.byte_count + 1U;
  navigation.transition.invertible = true;
  navigation.transition.determinant_negative = true;
  navigation.transition.determinant_magnitude = 257U - (encoded.query_face + 1U);
  navigation.transition.sequence_first = sequence_first;
  navigation.transition.sequence_second = sequence_second;
  navigation.transition.projected_first =
      (static_cast<std::uint64_t>(encoded.query_face) + 1U) * sequence_first + sequence_second;
  navigation.transition.projected_second = 257U * sequence_first + sequence_second;
  navigation.overlap.occurrence = occurrence_seed + selected;
  navigation.overlap.projection_chart = variant.owner_seed + 6'000'000U;
  navigation.overlap.sequence_chart = variant.owner_seed + 6'000'001U;
  navigation.overlap.same_source_occurrence = true;
}

[[nodiscard]] bool equal_navigation(
    const receiver::navigation_receipt& a,
    const receiver::navigation_receipt& b) noexcept {
  if (a.preimage.state != b.preimage.state || a.preimage.face != b.preimage.face ||
      a.preimage.projection_words_touched != b.preimage.projection_words_touched ||
      a.preimage.occurrences_touched != b.preimage.occurrences_touched ||
      a.preimage.occurrence_fold != b.preimage.occurrence_fold ||
      a.preimage.selected_occurrence != b.preimage.selected_occurrence ||
      a.support.occurrence_count != b.support.occurrence_count ||
      a.support.relation_count != b.support.relation_count ||
      a.support.source_occurrence_count != b.support.source_occurrence_count ||
      a.support.source_relation_count != b.support.source_relation_count ||
      a.transition.invertible != b.transition.invertible ||
      a.transition.determinant_negative != b.transition.determinant_negative ||
      a.transition.determinant_magnitude != b.transition.determinant_magnitude ||
      a.transition.sequence_first != b.transition.sequence_first ||
      a.transition.sequence_second != b.transition.sequence_second ||
      a.transition.projected_first != b.transition.projected_first ||
      a.transition.projected_second != b.transition.projected_second ||
      a.overlap.occurrence != b.overlap.occurrence ||
      a.overlap.projection_chart != b.overlap.projection_chart ||
      a.overlap.sequence_chart != b.overlap.sequence_chart ||
      a.overlap.same_source_occurrence != b.overlap.same_source_occurrence ||
      a.obstruction.state != b.obstruction.state ||
      a.obstruction.face != b.obstruction.face ||
      a.obstruction.projection_words_touched != b.obstruction.projection_words_touched ||
      a.obstruction.occurrences_touched != b.obstruction.occurrences_touched ||
      a.source_bytes_visible_to_query != b.source_bytes_visible_to_query) {
    return false;
  }
  for (std::size_t slot = 0; slot < 5; ++slot) {
    if (a.support.occurrence_identities[slot] != b.support.occurrence_identities[slot] ||
        a.support.payloads[slot] != b.support.payloads[slot]) {
      return false;
    }
  }
  return true;
}

}  // namespace

apparatus::source_topology_output r3_oracle(
    const codec::source_environment& environment) noexcept {
  apparatus::source_topology_output expected{};
  const auto& encoded = environment.encoded();
  std::uint64_t occurrence_fold = 0;
  std::uint64_t relation_fold = 0;
  for (std::size_t source_slot = 0; source_slot < encoded.source_count; ++source_slot) {
    const auto source = encoded.sources[source_slot];
    for (std::size_t local = 0; local < source.byte_count; ++local) {
      const std::size_t global = source.byte_begin + local;
      occurrence_fold ^= record_hash(20'000'000U + global,
          21'000'000U + source_slot, local, encoded.bytes[global]);
      if (local + 1 < source.byte_count) {
        const std::size_t relation = source.relation_begin + local;
        const std::uint64_t label = static_cast<std::uint64_t>(encoded.bytes[global]) * 256U +
            encoded.bytes[global + 1];
        relation_fold ^= record_hash(relation, global, global + 1, label);
      }
    }
  }
  for (std::size_t slot = 0; slot < codec::source_variant_capacity; ++slot) {
    auto& variant = expected.variants[slot];
    variant.population.source_count = encoded.source_count;
    variant.population.occurrence_count = encoded.byte_count;
    variant.population.relation_count = encoded.relation_count;
    variant.population.occurrence_fold = exact::word{occurrence_fold};
    variant.population.relation_fold = exact::word{relation_fold};
    variant.transduction.chunks = encoded.variants[slot].chunk_count;
    variant.transduction.local_relations = static_cast<std::uint16_t>(
        encoded.relation_count - encoded.variants[slot].chunk_count + encoded.source_count);
    variant.transduction.cross_cut_relations = static_cast<std::uint16_t>(
        encoded.variants[slot].chunk_count - encoded.source_count);
    variant.transduction.boundary_summaries = encoded.variants[slot].chunk_count;
    variant.transduction.source_bytes_visible = encoded.byte_count;
    variant.transduction.pair_fold = relation_fold;
    fill_navigation(encoded, encoded.variants[slot], variant.navigation);
  }
  expected.semantic_occurrence_invariant = true;
  expected.semantic_relation_invariant = true;
  expected.detached_query_returned = true;
  return expected;
}

std::size_t r3_environment_failures(
    const codec::source_environment& original,
    const codec::source_environment& relocated,
    const apparatus::source_store_receipt& original_receipt,
    const apparatus::source_store_receipt& relocated_receipt) noexcept {
  if (!apparatus::same_source_material(original, relocated) ||
      original_receipt.state != apparatus::source_store_status::exact ||
      relocated_receipt.state != apparatus::source_store_status::exact ||
      original_receipt.byte_testimony_fold != relocated_receipt.byte_testimony_fold ||
      original_receipt.path_testimony_fold == relocated_receipt.path_testimony_fold) {
    return 1;
  }
  const auto& encoded = original.encoded();
  std::size_t failures = 0;
  constexpr std::uint16_t apertures[codec::source_variant_capacity]{31U, 64U, 127U, 257U};
  for (std::size_t variant_slot = 0; variant_slot < codec::source_variant_capacity; ++variant_slot) {
    std::uint8_t occurrence_cover[codec::source_byte_capacity]{};
    std::uint8_t relation_cover[codec::source_byte_capacity]{};
    const auto variant = encoded.variants[variant_slot];
    if (variant.chunk_aperture != apertures[variant_slot] ||
        variant.ingestion_order != variant_slot) {
      ++failures;
    }
    for (std::size_t relative = 0; relative < variant.chunk_count; ++relative) {
      const std::size_t chunk_slot = variant.chunk_begin + relative;
      const auto chunk = encoded.chunks[chunk_slot];
      if (chunk.source_slot >= encoded.source_count || chunk.byte_count == 0 ||
          chunk.local_begin + chunk.byte_count > encoded.sources[chunk.source_slot].byte_count) {
        ++failures;
        continue;
      }
      const auto source = encoded.sources[chunk.source_slot];
      for (std::size_t local = chunk.local_begin;
           local < static_cast<std::size_t>(chunk.local_begin) + chunk.byte_count; ++local) {
        ++occurrence_cover[source.byte_begin + local];
        if (local + 1 < static_cast<std::size_t>(chunk.local_begin) + chunk.byte_count) {
          ++relation_cover[source.relation_begin + local];
        }
      }
      if (chunk.next_chunk != codec::no_chunk_slot) {
        const auto next = encoded.chunks[chunk.next_chunk];
        if (next.source_slot != chunk.source_slot ||
            next.local_begin != chunk.local_begin + chunk.byte_count) {
          ++failures;
        } else {
          ++relation_cover[source.relation_begin + chunk.local_begin + chunk.byte_count - 1];
        }
      }
    }
    for (std::size_t slot = 0; slot < encoded.byte_count; ++slot) {
      if (occurrence_cover[slot] != 1) { ++failures; }
    }
    for (std::size_t slot = 0; slot < encoded.relation_count; ++slot) {
      if (relation_cover[slot] != 1) { ++failures; }
    }
  }
  return failures;
}

std::size_t r3_verification_failures(
    const apparatus::source_topology_output& expected,
    const apparatus::source_topology_output& returned,
    const apparatus::source_topology_executor_receipt& execution) noexcept {
  std::size_t failures = execution.returned() ? 0 : 1;
  for (std::size_t slot = 0; slot < codec::source_variant_capacity; ++slot) {
    const auto& a = expected.variants[slot];
    const auto& b = returned.variants[slot];
    if (a.population.state != b.population.state ||
        a.population.source_count != b.population.source_count ||
        a.population.occurrence_count != b.population.occurrence_count ||
        a.population.relation_count != b.population.relation_count ||
        a.population.occurrence_fold != b.population.occurrence_fold ||
        a.population.relation_fold != b.population.relation_fold ||
        a.transduction.state != b.transduction.state ||
        a.transduction.chunks != b.transduction.chunks ||
        a.transduction.local_relations != b.transduction.local_relations ||
        a.transduction.cross_cut_relations != b.transduction.cross_cut_relations ||
        a.transduction.boundary_summaries != b.transduction.boundary_summaries ||
        a.transduction.source_bytes_visible != b.transduction.source_bytes_visible ||
        a.transduction.pair_fold != b.transduction.pair_fold ||
        !equal_navigation(a.navigation, b.navigation)) {
      ++failures;
    }
  }
  if (expected.semantic_occurrence_invariant != returned.semantic_occurrence_invariant ||
      expected.semantic_relation_invariant != returned.semantic_relation_invariant ||
      expected.detached_query_returned != returned.detached_query_returned ||
      returned.source_mismatches != 0 || returned.occurrence_mismatches != 0 ||
      returned.relation_mismatches != 0 || returned.direct_oracle_mismatches != 0) {
    ++failures;
  }
  return failures;
}

}  // namespace holonics::tests
