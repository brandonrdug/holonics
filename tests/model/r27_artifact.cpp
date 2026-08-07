#include "r27_artifact.hpp"

#include <ostream>

namespace holonics::tests {
void write_r27_artifact(std::ostream& out, bool source_loaded,
    const apparatus::expression_geometry_store_receipt& source_load,
    const apparatus::expression_geometry_store_receipt& rest_load,
    const apparatus::expression_geometry_store_receipt& rest_write,
    const apparatus::expression_geometry_executor_receipt& execution,
    const event::expression_geometry_observation& observation,
    const event::expression_geometry_rest_record& handoff, std::size_t failures) {
  const auto& inquiry = observation.inquiry; const auto& canonical = inquiry.presentations[0];
  out << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "hodge_conjecture_status=outside-aperture\n"
      << "riemann_hypothesis_status=outside-aperture\n"
      << "program=r27_expression_to_geometry_differential_transport.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\nsemantic_threads=" << execution.semantic_threads.value()
      << "\nbytes_to_device=" << execution.bytes_to_device.value()
      << "\nbytes_from_device=" << execution.bytes_from_device.value()
      << "\nresident_bytes=" << execution.resident_bytes.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nverification_failures=" << failures
      << "\nexecutor_state=" << static_cast<unsigned>(execution.state)
      << "\npredecessor_remount=body:" << observation.predecessor_remount.body.returned
      << ",same_body:" << observation.predecessor_remount.same_body
      << ",theory:" << observation.predecessor_remount.theory_preserved
      << ",source_replayed:" << observation.predecessor_remount.source_replayed
      << ",theory_id:" << observation.predecessor_remount.theory.value()
      << "\ninquiry=all_exact:" << inquiry.all_exact << ",theory_formed:"
      << inquiry.theory_formed << ",source_mask:" << inquiry.theory.source_mask
      << ",obstruction:" << static_cast<unsigned>(inquiry.obstruction)
      << ",no_expected_invariants:" << inquiry.no_expected_invariants
      << "\nsource_card=loaded:" << source_loaded << ",bytes:" << source_load.bytes.value()
      << ",fold:" << source_load.byte_fold << ",path_fold:" << source_load.path_fold
      << "\nsource_aperture=presentations:3,variables:3,terms:12,degree:5,sylvester:9x9,"
         "module_rank:4,series_depth:11,expected_invariants:absent\n";
  for (std::uint8_t slot = 0; slot < 3; ++slot) {
    const auto& value = inquiry.presentations[slot];
    out << "presentation_" << static_cast<unsigned>(slot) << "=terms:"
        << static_cast<unsigned>(value.mounted.term_count) << ",shift:"
        << static_cast<int>(value.ideal.chart_shift) << ",b:" << value.ideal.constant_parameter
        << ",singulars:" << static_cast<unsigned>(value.ideal.geometric_singular_count)
        << ",resultant:" << value.ideal.resultant.coefficients[0] << ','
        << value.ideal.resultant.coefficients[5] << ",resultant_mask:"
        << value.ideal.resultant_sample_mask << ",bezout_mask:"
        << value.ideal.bezout_sample_mask << ",sample0:"
        << value.ideal.resultant_samples[0] << ",basis_rank:"
        << static_cast<unsigned>(value.connection.rank) << ",samples:"
        << static_cast<unsigned>(value.sample_count) << ",exact:" << value.exact << '\n';
  }
  out << "scalar=order:" << static_cast<unsigned>(canonical.scalar.order)
      << ",coefficients:" << canonical.scalar.coefficients[4].coefficients[0] << ','
      << canonical.scalar.coefficients[4].coefficients[5] << ','
      << canonical.scalar.coefficients[3].coefficients[4] << ','
      << canonical.scalar.coefficients[2].coefficients[3] << ','
      << canonical.scalar.coefficients[1].coefficients[2] << ','
      << canonical.scalar.coefficients[0].coefficients[1]
      << ",recurrence_exact:" << canonical.scalar.recurrence_exact << '\n'
      << "indicial=finite:0,0,2,-3,1,infinity:";
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (slot != 0) { out << ','; } out << canonical.indicial.infinity_coefficients[slot];
  }
  out << ",regular_singular:" << canonical.indicial.regular_singular
      << "\nresidue=relation:4a5=" << canonical.residue.relation_constant
      << ",nonzero:" << canonical.residue.nonzero << ",rank_one:"
      << canonical.residue.rank_one << ",square_zero:" << canonical.residue.square_zero
      << ",log_channel:" << canonical.residue.logarithmic_channel
      << "\nexpression_fiber=members:" << static_cast<unsigned>(inquiry.invariant_fiber.member_count)
      << ",rational_rechart:" << inquiry.rational_rechart.exact << ",shift:"
      << static_cast<int>(inquiry.rational_rechart.x_shift) << ",gaussian_rechart:"
      << inquiry.gaussian_rechart.exact << ",field_dependency:"
      << inquiry.gaussian_rechart.field_dependency_retained
      << "\nchanged=b:2,resultant:" << observation.changed.presentations[0].ideal.resultant.coefficients[0]
      << ',' << observation.changed.presentations[0].ideal.resultant.coefficients[5]
      << ",series_changed:" << observation.changed.series_changed
      << ",source_sensitive:" << observation.changed.source_sensitive
      << "\nchecker=exit:" << observation.passage.raw.exit_status
      << ",stdout_bytes:" << observation.passage.raw.stdout_bytes
      << ",stderr_bytes:" << observation.passage.raw.stderr_bytes
      << ",produced_bytes:" << observation.passage.raw.produced_artifact_bytes
      << "\nfinal_body=head:" << observation.final_head.value() << ",continuation:"
      << observation.final_continuation.value()
      << ",rest_bytes:" << rest_write.bytes.value() << ",integrity:" << handoff.integrity
      << "\nrest_io=loaded:" << rest_load.returned() << ",written:" << rest_write.returned()
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  out.write(observation.passage.formal.bytes, observation.passage.formal.byte_count);
  out << "formal_end\nconversation_begin\n";
  out.write(observation.passage.conversational.bytes,
      observation.passage.conversational.byte_count);
  out << "\nconversation_end\nchecker_stdout_begin\n";
  out.write(observation.passage.raw.standard_output, observation.passage.raw.stdout_bytes);
  out << "checker_stdout_end\n";
}

}  // namespace holonics::tests
