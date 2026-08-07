#include "r21_artifact.hpp"

#include <ostream>

namespace holonics::tests {
void write_r21_artifact(std::ostream& output,
    const apparatus::blind_store_receipt& code_load,
    const apparatus::blind_store_receipt& moment_load,
    const apparatus::blind_store_receipt& rest_load,
    const apparatus::blind_store_receipt& rest_write,
    const apparatus::blind_reconstruction_executor_receipt& execution,
    const apparatus::blind_probe_receipt& code_probe,
    const apparatus::blind_probe_receipt& moment_probe,
    const event::blind_reconstruction_observation& value,
    const event::blind_reconstruction_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\n"
      << "formal_evidence=formal-checked\n"
      << "comparison_truth_status=pending-post-return\n"
      << "historical_truth_status=historical\n"
      << "program=r21_blind_characteristic_reconstruction.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\ncode_threads=" << execution.code_threads.value()
      << "\nmoment_threads=" << execution.moment_threads.value()
      << "\nbytes_to_device=" << execution.bytes_to_device.value()
      << "\nbytes_from_device=" << execution.bytes_from_device.value()
      << "\nresident_bytes=" << execution.resident_bytes.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nreleased_solution_reads=" << execution.released_solution_reads.value()
      << "\nlogical_read_support=" << execution.logical.read_support.value()
      << "\nlogical_change_support=" << execution.logical.change_support.value()
      << "\nlogical_alternatives=" << execution.logical.alternatives_retained.value()
      << "\nlogical_obstructions=" << execution.logical.obstructions_retained.value()
      << "\nverification_failures=" << failures
      << "\nsource_cards=code_bytes:" << code_load.bytes.value() << ",code_fold:"
      << code_load.byte_fold << ",code_path_fold:" << code_load.path_fold
      << ",moment_bytes:" << moment_load.bytes.value() << ",moment_fold:"
      << moment_load.byte_fold << ",moment_path_fold:" << moment_load.path_fold
      << "\nsource_aperture=released_solution:absent,expected_operator:absent,expected_roots:absent"
      << "\npredecessor=rest_bytes:" << rest_load.bytes.value() << ",head:14001012"
      << "\ncode=vertices:" << inquiry.code.vertex_count << ",codewords:"
      << +inquiry.code.codeword_count << ",minimum_distance:" << +inquiry.code.minimum_distance
      << ",returned_pairs:" << +inquiry.returned_pairs
      << "\npair_shapes=d3:" << +inquiry.pairs[0].left_size << 'x'
      << +inquiry.pairs[0].right_size << ",d4:" << +inquiry.pairs[1].left_size << 'x'
      << +inquiry.pairs[1].right_size << ",d7:" << +inquiry.pairs[2].left_size << 'x'
      << +inquiry.pairs[2].right_size << ",mass_adjoint:1,commuting_directions:1"
      << "\nmoment0=det:" << inquiry.moments[0].hankel_determinant << ",disc:"
      << inquiry.moments[0].discriminant << ",roots:" << inquiry.moments[0].roots[0] << ','
      << inquiry.moments[0].roots[1] << ',' << inquiry.moments[0].roots[2]
      << "\nmoment1=det:" << inquiry.moments[1].hankel_determinant << ",disc:"
      << inquiry.moments[1].discriminant << ",roots:" << inquiry.moments[1].roots[0] << ','
      << inquiry.moments[1].roots[1] << ',' << inquiry.moments[1].roots[2]
      << "\nmoment2=det:" << inquiry.moments[2].hankel_determinant << ",disc:"
      << inquiry.moments[2].discriminant << ",roots:" << inquiry.moments[2].roots[0] << ','
      << inquiry.moments[2].roots[1] << ',' << inquiry.moments[2].roots[2] << ','
      << inquiry.moments[2].roots[3]
      << "\ncontrols=collision_det:" << inquiry.moments[3].hankel_determinant
      << ",collision_disc:" << inquiry.moments[3].discriminant << ",short_access:"
      << inquiry.moments[4].access_complete << ",code_gpu_probe:" << code_probe.returned()
      << ",moment_gpu_probe:" << moment_probe.returned()
      << "\ncode_checker=exit:" << value.code.raw.exit_status << ",stdout_bytes:"
      << value.code.raw.stdout_bytes << ",stderr_bytes:" << value.code.raw.stderr_bytes
      << ",produced_bytes:" << value.code.raw.produced_artifact_bytes << ",source_fold:"
      << value.code.raw.source_fold << ",artifact_fold:" << value.code.raw.produced_artifact_fold
      << "\nmoment_checker=exit:" << value.moment.raw.exit_status << ",stdout_bytes:"
      << value.moment.raw.stdout_bytes << ",stderr_bytes:" << value.moment.raw.stderr_bytes
      << ",produced_bytes:" << value.moment.raw.produced_artifact_bytes << ",source_fold:"
      << value.moment.raw.source_fold << ",artifact_fold:"
      << value.moment.raw.produced_artifact_fold
      << "\nfinal_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",rest_bytes:" << rest_write.bytes.value()
      << ",integrity:" << handoff.integrity
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\ncode_formal_begin\n";
  output.write(value.code.formal.bytes, value.code.formal.byte_count);
  output << "code_formal_end\ncode_conversation_begin\n";
  output.write(value.code.conversational.bytes, value.code.conversational.byte_count);
  output << "code_conversation_end\nmoment_formal_begin\n";
  output.write(value.moment.formal.bytes, value.moment.formal.byte_count);
  output << "moment_formal_end\nmoment_conversation_begin\n";
  output.write(value.moment.conversational.bytes, value.moment.conversational.byte_count);
  output << "moment_conversation_end\ncode_stdout_begin\n";
  output.write(value.code.raw.standard_output, value.code.raw.stdout_bytes);
  output << "code_stdout_end\nmoment_stdout_begin\n";
  output.write(value.moment.raw.standard_output, value.moment.raw.stdout_bytes);
  output << "moment_stdout_end\n";
}

}  // namespace holonics::tests
