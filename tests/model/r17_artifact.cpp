#include "r17_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r17_artifact(std::ostream& output,
    const apparatus::geometry_store_receipt& rest_load,
    const apparatus::geometry_store_receipt& rest_write,
    const apparatus::geometry_inquiry_executor_receipt& execution,
    const event::geometry_inquiry_observation& value,
    const event::geometry_inquiry_rest_record& handoff,
    const apparatus::sealed_geometry_comparison& comparison,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  const auto& process = execution.process;
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness,formal-checked\n"
         << "program=r17_agnostic_geometry_inquiry.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "probe_threads=" << execution.probe_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "engine_source_reads=" << execution.engine_source_reads.value() << '\n'
         << "exterior_retrieval_calls=" << execution.exterior_retrieval_calls.value() << '\n'
         << "developmental_source_bytes=" << execution.developmental_source_bytes.value() << '\n'
         << "verification_failures=" << failures << '\n'
         << "question=identity:" << inquiry.question.identity.value()
         << ",receiver:" << inquiry.question.receiver.value()
         << ",material:" << inquiry.question.material.value() << '\n'
         << "question_aperture=mode_field_absent:" << inquiry.mode_field_absent
         << ",expected_answer_absent:" << inquiry.expected_answer_absent
         << ",historical_reference_absent:1\n"
         << "native_input=rest_bytes:" << rest_load.bytes.value()
         << ",source_bytes:0,retrieval_handles:0\n"
         << "local_front=returned:" << inquiry.returned_probe_count
         << ",projective:" << inquiry.projective_probe_count
         << ",coordinate_counterexamples:" << inquiry.coordinate_counterexamples
         << ",singular:" << inquiry.singular_probe_count
         << ",global_scans:" << inquiry.global_candidate_scans << '\n'
         << "symbolic_difference=alpha_gamma_xy_cancelled:"
         << inquiry.symbolic.alpha_gamma_xy_cancelled
         << ",beta_delta_cancelled:" << inquiry.symbolic.beta_delta_cancelled
         << ",determinant_factored:" << inquiry.symbolic.determinant_factored
         << ",four_point_cancellation:"
         << inquiry.symbolic.complete_four_point_cancellation << '\n'
         << "fibers=raw_coordinate:obstructed,affine_common_square:closed,"
            "fractional_cross_ratio:closed,singular_quotient:obstructed\n"
         << "theory=passage:" << inquiry.theory.passage.value()
         << ",difference_factor:" << inquiry.theory.difference_factor
         << ",affine_common_square:" << inquiry.theory.affine_common_square
         << ",fractional_invariance:" << inquiry.theory.fractional_invariance
         << ",coordinate_counterexample:" << inquiry.theory.coordinate_counterexample
         << ",singular_boundary:" << inquiry.theory.singular_boundary << '\n'
         << "formation_delta=head:" << value.theory_commit.predecessor.value() << ':'
         << value.theory_commit.successor.value() << ",morphology:"
         << value.theory_commit.admitted_tally_before << ':'
         << value.theory_commit.admitted_tally_after << '\n'
         << "checker=exit:" << value.raw.exit_status
         << ",stdout_bytes:" << value.raw.stdout_bytes
         << ",stderr_bytes:" << value.raw.stderr_bytes
         << ",produced_bytes:" << value.raw.produced_artifact_bytes
         << ",declarations:" << value.typed.produced_declarations
         << ",remaining_goals:" << value.typed.remaining_goal_count
         << ",kernel:" << value.typed.kernel_boundary_crossed
         << ",calls:" << process.exterior_process_calls.value() << '\n'
         << "return_delta=mathematical:"
         << value.returned_morphology.mathematical_before << ':'
         << value.returned_morphology.mathematical_after << ",codec:"
         << value.returned_morphology.codec_before << ':'
         << value.returned_morphology.codec_after << ",geometry:0:"
         << handoff.geometry_admitted_tally << ",body:"
         << value.returned_morphology.commit.admitted_tally_before << ':'
         << value.returned_morphology.commit.admitted_tally_after << '\n'
         << "sealed_comparison=opened_after_return:" << comparison.opened_after_kernel_return
         << ",observer_reads:" << comparison.observer_reads.value()
         << ",engine_reads:" << comparison.engine_reads.value()
         << ",affine_neighbor:" << comparison.affine_neighbor_present
         << ",fractional_neighbor:" << comparison.fractional_neighbor_present
         << ",body_resumed:" << comparison.body_resumed_after_open
         << ",bytes:" << comparison.bytes.value()
         << ",fold:" << comparison.content_fold << '\n'
         << "final_body=head:" << handoff.body.head
         << ",continuation:" << handoff.body.continuation
         << ",body_admitted_tally:" << handoff.body.regions[0].morphology
         << ",mathematical:" << handoff.mathematical_admitted_tally
         << ",codec:" << handoff.codec_admitted_tally
         << ",geometry:" << handoff.geometry_admitted_tally
         << ",rest_bytes:" << rest_write.bytes.value()
         << ",integrity:" << handoff.integrity << '\n'
         << "logical_work=read_support:" << execution.logical.read_support.value()
         << ",change_support:" << execution.logical.change_support.value()
         << ",alternatives:" << execution.logical.alternatives_retained.value()
         << ",obstructions:" << execution.logical.obstructions_retained.value()
         << ",reservations:" << execution.logical.reservations_consumed.value() << '\n'
         << "physical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
            "power:unknown,energy:unknown\n"
         << "formal_begin\n";
  output.write(value.formal.bytes, value.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(value.conversational.bytes, value.conversational.byte_count);
  output << "conversation_end\nstdout_begin\n";
  output.write(value.raw.standard_output, value.raw.stdout_bytes);
  output << "stdout_end\nstderr_begin\n";
  output.write(value.raw.standard_error, value.raw.stderr_bytes);
  output << "stderr_end\n";
}

}  // namespace holonics::tests
