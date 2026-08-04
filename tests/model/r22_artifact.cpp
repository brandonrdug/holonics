#include "r22_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void write_coefficients(std::ostream& output,
    const organ::cm_graph_receipt& graph) noexcept {
  for (std::size_t slot = 0; slot < organ::cm_characteristic_capacity; ++slot) {
    if (slot != 0) { output << ','; }
    output << graph.characteristic[slot];
  }
}

}  // namespace

void write_r22_artifact(std::ostream& output,
    const apparatus::cm_store_receipt& card_load,
    const apparatus::cm_store_receipt& rest_load,
    const apparatus::cm_store_receipt& rest_write,
    const apparatus::cm_executor_receipt& execution,
    const apparatus::cm_probe_receipt& probe,
    const organ::cm_incidence_receipt& changed,
    const event::cm_incidence_observation& value,
    const event::cm_incidence_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\n"
      << "formal_evidence=formal-checked\n"
      << "published_theorem_status=outside-aperture\n"
      << "historical_truth_status=historical\n"
      << "program=r22_cm_norm_one_arithmetic_incidence.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\narithmetic_threads=" << execution.arithmetic_threads.value()
      << "\ncharacteristic_threads=" << execution.characteristic_threads.value()
      << "\nbytes_to_device=" << execution.bytes_to_device.value()
      << "\nbytes_from_device=" << execution.bytes_from_device.value()
      << "\nresident_bytes=" << execution.resident_bytes.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nlogical_read_support=" << execution.logical.read_support.value()
      << "\nlogical_change_support=" << execution.logical.change_support.value()
      << "\nlogical_alternatives=" << execution.logical.alternatives_retained.value()
      << "\nlogical_obstructions=" << execution.logical.obstructions_retained.value()
      << "\nverification_failures=" << failures
      << "\nsource_card=bytes:" << card_load.bytes.value() << ",fold:" << card_load.byte_fold
      << ",path_fold:" << card_load.path_fold
      << "\nsource_aperture=order:" << +inquiry.mounted.cyclotomic_order << ",degree:"
      << +inquiry.mounted.degree << ",periodic_modulus:" << +inquiry.mounted.periodic_modulus
      << ",window:" << +inquiry.mounted.window_min << ':' << +inquiry.mounted.window_max
      << ",translations:" << +inquiry.mounted.translation_count
      << ",expected_incidence:absent,expected_spectrum:absent"
      << "\npredecessor=rest_bytes:" << rest_load.bytes.value() << ",head:14001016"
      << "\ntranslation_return=count:" << +inquiry.returned_translations
      << ",all_norm_one:" << inquiry.theory.norm_one
      << "\nperiodic=vertices:16,edges:" << +inquiry.periodic.edge_count
      << ",factors:" << +inquiry.periodic.factor_count
      << ",commuting_characters:1"
      << "\nwindow=vertices:16,edges:" << +inquiry.window.edge_count
      << ",unit_pairs:" << +inquiry.projection.unit_pair_count
      << ",lost:" << +inquiry.projection.lost_count
      << ",projection_loss:" << +inquiry.projection.projection_loss
      << ",factors:" << +inquiry.window.factor_count
      << "\ndirection_population=" << +inquiry.projection.direction_population[0] << ','
      << +inquiry.projection.direction_population[1] << ','
      << +inquiry.projection.direction_population[2] << ','
      << +inquiry.projection.direction_population[3] << ','
      << +inquiry.projection.direction_population[4]
      << "\nscattering=commutator_nonzero:"
      << +inquiry.scattering.commutator_nonzero[0] << ','
      << +inquiry.scattering.commutator_nonzero[1] << ','
      << +inquiry.scattering.commutator_nonzero[2] << ','
      << +inquiry.scattering.commutator_nonzero[3]
      << ",coefficient_sum_images:" << +inquiry.projection.distinct_scalar_sums
      << "\nprobe=returned:" << probe.returned() << ",translation_count:"
      << +changed.returned_translations << ",periodic_edges:"
      << +changed.periodic.edge_count << ",window_edges:" << +changed.window.edge_count
      << ",lost:" << +changed.projection.lost_count
      << "\nprobe_periodic_characteristic=";
  write_coefficients(output, changed.periodic);
  output << "\nprobe_window_characteristic=";
  write_coefficients(output, changed.window);
  output << "\nchecker=exit:" << value.passage.raw.exit_status << ",stdout_bytes:"
      << value.passage.raw.stdout_bytes << ",stderr_bytes:" << value.passage.raw.stderr_bytes
      << ",produced_bytes:" << value.passage.raw.produced_artifact_bytes << ",source_fold:"
      << value.passage.raw.source_fold << ",artifact_fold:"
      << value.passage.raw.produced_artifact_fold
      << "\nfinal_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",morphology:" << handoff.body.regions[0].morphology
      << ",mathematical:" << handoff.mathematical_morphology << ",codec:"
      << handoff.codec_morphology << ",cm_incidence:" << handoff.cm_incidence_morphology
      << ",rest_bytes:" << rest_write.bytes.value() << ",integrity:" << handoff.integrity
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  output.write(value.passage.formal.bytes, value.passage.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(value.passage.conversational.bytes, value.passage.conversational.byte_count);
  output << "conversation_end\nchecker_stdout_begin\n";
  output.write(value.passage.raw.standard_output, value.passage.raw.stdout_bytes);
  output << "checker_stdout_end\n";
}

}  // namespace holonics::tests
