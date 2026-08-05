#include "r28_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r28_artifact(std::ostream& out, bool source_loaded,
    const apparatus::hodge_store_receipt& source_load,
    const apparatus::hodge_store_receipt& rest_load,
    const apparatus::hodge_store_receipt& rest_write,
    const apparatus::hodge_executor_receipt& execution,
    const event::hodge_realization_observation& observation,
    const event::hodge_realization_rest_record& handoff, std::size_t failures) {
  const auto& inquiry = observation.inquiry; const auto& locus = inquiry.cycles.locus;
  out << "truth_status=established-bounded\nevidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "hodge_conjecture_status=outside-aperture\nriemann_hypothesis_status=outside-aperture\n"
      << "program=r28_hodge_realization.sm_89\ndevice_compute_capability="
      << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\nsemantic_threads=" << execution.semantic_threads.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nverification_failures=" << failures
      << "\nexecutor_state=" << static_cast<unsigned>(execution.state)
      << "\nsource_card=loaded:" << source_loaded << ",bytes:" << source_load.bytes.value()
      << ",fold:" << source_load.byte_fold << ",path_fold:" << source_load.path_fold
      << "\npredecessor_remount=body:" << observation.predecessor_remount.body.returned
      << ",same_body:" << observation.predecessor_remount.same_body
      << ",theory:" << observation.predecessor_remount.theory_preserved
      << ",source_replayed:" << observation.predecessor_remount.source_replayed
      << "\nfamily=legendre_product,factors:2,rank:" << static_cast<unsigned>(inquiry.product.rational_rank)
      << ",hodge:" << static_cast<unsigned>(inquiry.product.h20) << ','
      << static_cast<unsigned>(inquiry.product.h11) << ','
      << static_cast<unsigned>(inquiry.product.h02)
      << ",denominator:" << inquiry.product.common_denominator
      << "\ntransport=cup_t:" << inquiry.product.connection_t_preserves_cup
      << ",cup_u:" << inquiry.product.connection_u_preserves_cup
      << ",mixed_zero:" << inquiry.product.mixed_curvature_zero
      << ",griffiths:" << inquiry.product.griffiths_transverse
      << "\nlocus=quotient:" << locus.quotient_obstruction[0] << ','
      << locus.quotient_obstruction[1] << ",tangent:" << locus.tangent_obstruction
      << ",normal:" << locus.normal_obstruction << ",multiplicity:"
      << static_cast<unsigned>(locus.multiplicity) << ",graph_square:" << locus.graph_square
      << ",mutual:" << locus.mutual_intersection << ",primitive_square:" << locus.primitive_square
      << "\ncycles=generators:" << static_cast<unsigned>(inquiry.cycles.generator_count)
      << ",translations:4,distinct:" << inquiry.cycles.translations_distinct
      << ",enumerated:" << inquiry.cycles.fibers[0].enumerated
      << ",integral_realizers:" << static_cast<unsigned>(inquiry.cycles.fibers[0].realizer_count)
      << ",half_realizers:" << static_cast<unsigned>(inquiry.cycles.fibers[1].realizer_count)
      << ",effective_graphs:" << static_cast<unsigned>(inquiry.cycles.fibers[0].effective_count)
      << ",outside_obstructed:" << inquiry.cycles.fibers[2].outside_image
      << "\nblowup=rank:" << static_cast<unsigned>(inquiry.blowup.rank)
      << ",exceptional_square:" << inquiry.blowup.pairing[6][6]
      << ",center:" << static_cast<unsigned>(inquiry.blowup.center_selector)
      << ",selected_square:" << inquiry.blowup.self_intersections[0]
      << ",changed_center:" << static_cast<unsigned>(observation.changed.center_selector)
      << ",changed_selected_square:" << observation.changed.self_intersections[1]
      << "\nchecker=exit:" << observation.passage.raw.exit_status
      << ",stdout_bytes:" << observation.passage.raw.stdout_bytes
      << ",stderr_bytes:" << observation.passage.raw.stderr_bytes
      << ",produced_bytes:" << observation.passage.raw.produced_artifact_bytes
      << "\nfinal_body=head:" << observation.final_head.value() << ",continuation:"
      << observation.final_continuation.value() << ",morphology:"
      << handoff.body.regions[0].morphology << ",mathematical:"
      << handoff.mathematical_morphology << ",codec:" << handoff.codec_morphology
      << ",hodge:" << handoff.hodge_realization_morphology
      << ",rest_bytes:" << rest_write.bytes.value() << ",integrity:" << handoff.integrity
      << "\nrest_io=loaded:" << rest_load.returned() << ",written:" << rest_write.returned()
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  out.write(observation.passage.formal.bytes, observation.passage.formal.byte_count);
  out << "formal_end\nconversation_begin\n";
  out.write(observation.passage.conversational.bytes, observation.passage.conversational.byte_count);
  out << "\nconversation_end\nchecker_stdout_begin\n";
  out.write(observation.passage.raw.standard_output, observation.passage.raw.stdout_bytes);
  out << "checker_stdout_end\n";
}

}  // namespace holonics::tests
