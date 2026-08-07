#include "r3_artifact.hpp"

#include <cstddef>
#include <iomanip>
#include <ostream>

namespace holonics::tests {

void write_r3_artifact(
    std::ostream& output,
    const char* const* source_paths,
    std::size_t source_count,
    const apparatus::source_store_receipt& original_store,
    const apparatus::source_store_receipt& relocated_store,
    std::size_t environment_failures,
    const apparatus::source_topology_executor_receipt& execution,
    const apparatus::source_topology_output& returned,
    std::size_t verification_failures) {
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r3_incremental_foundation+detached_navigation.sm_89\n"
         << "source_count=" << source_count << '\n'
         << "source_bytes=" << original_store.byte_count << '\n';
  for (std::size_t slot = 0; slot < source_count; ++slot) {
    output << "source_" << slot << "=" << source_paths[slot] << '\n';
  }
  output << "path_testimony_distinct="
         << (original_store.path_testimony_fold != relocated_store.path_testimony_fold) << '\n'
         << "byte_testimony_fold=" << original_store.byte_testimony_fold << '\n'
         << "physical_placement_material_equal="
         << (original_store.byte_testimony_fold == relocated_store.byte_testimony_fold) << '\n'
         << "semantic_occurrence_invariant=" << returned.semantic_occurrence_invariant << '\n'
         << "semantic_relation_invariant=" << returned.semantic_relation_invariant << '\n'
         << "source_mismatches=" << returned.source_mismatches << '\n'
         << "occurrence_mismatches=" << returned.occurrence_mismatches << '\n'
         << "relation_mismatches=" << returned.relation_mismatches << '\n'
         << "direct_oracle_mismatches=" << returned.direct_oracle_mismatches << '\n'
         << "detached_query_returned=" << returned.detached_query_returned << '\n'
         << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_structure_bytes=" << execution.resident_structure_bytes.value() << '\n'
         << "resident_chart_bytes=" << execution.resident_chart_bytes.value() << '\n';
  constexpr unsigned apertures[codec::source_variant_capacity]{31U, 64U, 127U, 257U};
  for (std::size_t slot = 0; slot < codec::source_variant_capacity; ++slot) {
    const auto& variant = returned.variants[slot];
    output << "variant_" << slot << "_chunk_aperture=" << apertures[slot] << '\n'
           << "variant_" << slot << "_chunks=" << variant.transduction.chunks << '\n'
           << "variant_" << slot << "_local_relations="
           << variant.transduction.local_relations << '\n'
           << "variant_" << slot << "_cross_cut_relations="
           << variant.transduction.cross_cut_relations << '\n'
           << "variant_" << slot << "_occurrence_fold="
           << variant.population.occurrence_fold.value() << '\n'
           << "variant_" << slot << "_relation_fold="
           << variant.population.relation_fold.value() << '\n';
  }
  const auto& navigation = returned.variants[0].navigation;
  output << "query_face=" << static_cast<unsigned>(navigation.preimage.face) << '\n'
         << "query_projection_words_touched=" << navigation.preimage.projection_words_touched << '\n'
         << "query_preimage_occurrences_touched=" << navigation.preimage.occurrences_touched << '\n'
         << "query_selected_occurrence=" << navigation.preimage.selected_occurrence << '\n'
         << "query_local_occurrences_touched=" << navigation.support.occurrence_count << '\n'
         << "query_local_relations_touched=" << navigation.support.relation_count << '\n'
         << "query_source_occurrences=" << navigation.support.source_occurrence_count << '\n'
         << "query_source_relations=" << navigation.support.source_relation_count << '\n'
         << "query_neighborhood_hex=";
  output << std::hex << std::setfill('0');
  for (std::size_t slot = 0; slot < navigation.support.occurrence_count; ++slot) {
    output << std::setw(2) << static_cast<unsigned>(navigation.support.payloads[slot]);
  }
  output << std::dec << '\n'
         << "transition_invertible=" << navigation.transition.invertible << '\n'
         << "transition_determinant=-" << navigation.transition.determinant_magnitude << '\n'
         << "transition_sequence_pair=" << navigation.transition.sequence_first << ':'
         << navigation.transition.sequence_second << '\n'
         << "transition_projected_pair=" << navigation.transition.projected_first << ':'
         << navigation.transition.projected_second << '\n'
         << "overlap_same_source_occurrence=" << navigation.overlap.same_source_occurrence << '\n'
         << "obstruction_state=" << static_cast<unsigned>(navigation.obstruction.state) << '\n'
         << "obstruction_face=" << static_cast<unsigned>(navigation.obstruction.face) << '\n'
         << "source_bytes_visible_to_query=" << navigation.source_bytes_visible_to_query << '\n'
         << "environment_failures=" << environment_failures << '\n'
         << "verification_failures=" << verification_failures << '\n';
}

}  // namespace holonics::tests
