#include "r29_artifact.hpp"

#include <ostream>

namespace holonics::tests {
void write_r29_artifact(std::ostream& output, bool source_loaded,
    const apparatus::arithmetic_store_receipt& card,
    const apparatus::arithmetic_store_receipt& rest_load,
    const apparatus::arithmetic_store_receipt& rest_write,
    const apparatus::arithmetic_executor_receipt& execution,
    const event::arithmetic_spectral_observation& observation,
    const event::arithmetic_spectral_rest_record& handoff,
    std::size_t failures) {
  const auto& inquiry = observation.inquiry; const auto& passage = observation.passage;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "classical_riemann_hypothesis_status=outside-aperture\n"
      << "arbitrary_function_field_rh_status=outside-aperture\n"
      << "program=r29_arithmetic_spectral.sm_" << execution.device_major << execution.device_minor
      << "\ndevice_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\nsemantic_threads=" << execution.semantic_threads.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nverification_failures=" << failures
      << "\nexecutor_state=" << static_cast<unsigned>(execution.state)
      << "\nsource_card=loaded:" << source_loaded << ",bytes:" << card.bytes.value()
      << ",fold:" << card.byte_fold << ",path_fold:" << card.path_fold
      << "\npredecessor_remount=body:" << observation.predecessor_remount.body.returned
      << ",same_body:" << observation.predecessor_remount.same_body
      << ",theory:" << observation.predecessor_remount.theory_preserved
      << ",source_replayed:" << observation.predecessor_remount.source_replayed
      << "\nfields=p5_candidates:" << static_cast<unsigned>(inquiry.towers[0].candidate_count)
      << ",p13_candidates:" << static_cast<unsigned>(inquiry.towers[1].candidate_count)
      << ",exact:" << inquiry.towers[0].exact << ',' << inquiry.towers[1].exact;
  for (std::uint8_t slot = 0; slot < organ::arithmetic_curve_count; ++slot) {
    const auto& curve = inquiry.curves[slot];
    output << "\ncurve_" << static_cast<unsigned>(slot) << "=p:" << curve.source.prime
        << ",c:" << curve.source.coefficient << ",counts:" << curve.fixed_counts[0] << ','
        << curve.fixed_counts[1] << ',' << curve.fixed_counts[2] << ',' << curve.fixed_counts[3]
        << ",pi:" << curve.frobenius.real << ',' << curve.frobenius.imaginary
        << ",char:1," << -2 * curve.frobenius.real << ',' << curve.source.prime
        << ",places:" << curve.closed_places[0] << ',' << curve.closed_places[1] << ','
        << curve.closed_places[2] << ',' << curve.closed_places[3]
        << ",pointwise:" << curve.pointwise_points << ",bound:" << curve.correspondence_bound
        << ",exact:" << curve.exact;
  }
  output << "\ncontrols=twist5:" << inquiry.controls.twist_5_exact
      << ",twist13:" << inquiry.controls.twist_13_exact
      << ",changed_twist:" << inquiry.controls.changed_twist_exact
      << ",even:" << inquiry.controls.even_counts_preserved
      << ",odd:" << inquiry.controls.odd_counts_reversed
      << ",equal_factor_rechart:" << inquiry.controls.equal_factor_rechart
      << ",phase_separated:" << inquiry.controls.gaussian_phase_separated
      << ",archimedean_inapplicable:" << inquiry.controls.archimedean_inapplicable
      << "\ntheory=fixed:" << inquiry.theory.fixed_contributions
      << ",candidates:" << inquiry.theory.correspondence_candidates
      << ",points:" << inquiry.theory.correspondence_points
      << ",trace_currents:" << inquiry.theory.trace_currents
      << ",norm_currents:" << inquiry.theory.norm_currents
      << "\nchecker=exit:" << passage.raw.exit_status << ",stdout_bytes:"
      << passage.raw.stdout_bytes << ",stderr_bytes:" << passage.raw.stderr_bytes
      << ",produced_bytes:" << passage.raw.produced_artifact_bytes
      << "\nfinal_body=head:" << observation.final_head.value() << ",continuation:"
      << observation.final_continuation.value() << ",rest_bytes:" << sizeof(handoff)
      << ",integrity:" << handoff.integrity
      << "\nrest_io=loaded:" << rest_load.returned() << ",written:" << rest_write.returned()
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  output.write(passage.formal.bytes, passage.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(passage.conversational.bytes, passage.conversational.byte_count);
  output << "\nconversation_end\n";
}

}  // namespace holonics::tests
