#include "r16_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r16_artifact(std::ostream& output,
    const apparatus::theorem_rest_store_receipt& rest_load,
    const apparatus::dependent_setup_store_receipt& setup_load,
    const apparatus::first_return_artifact_testimony& first,
    const apparatus::terminal_theorem_executor_receipt& execution,
    const event::terminal_theorem_observation& value,
    const event::terminal_theorem_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& generation = value.generation;
  const auto& process = execution.process;
  const auto& environment = process.environment;
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r16_two_theorem_conversational_production.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "engine_source_reads=" << execution.engine_source_reads.value() << '\n'
         << "exterior_retrieval_calls=" << execution.exterior_retrieval_calls.value() << '\n'
         << "developmental_source_bytes=" << execution.developmental_source_bytes.value() << '\n'
         << "observer_artifact_reads=" << first.observer_artifact_reads.value() << '\n'
         << "verification_failures=" << failures << '\n'
         << "question_a=Given a situated algorithm, an invertible change of its state chart, and "
            "two composable execution traces in the original chart, produce and explain a theorem "
            "saying that their composite is a trace between the corresponding endpoints in the "
            "rebased chart.\n"
         << "question_b=After remounting the body changed by Deed A, take three composable "
            "execution traces in the original state chart. Produce and explain a theorem "
            "transporting the entire three-segment trace to the rebased chart. The proof must "
            "factor through the returned Deed A theorem fiber, not merely reconstruct an "
            "independent proof from the earlier library.\n"
         << "environment=toolchain_fold:" << environment.toolchain_fold
         << ",manifest_fold=" << environment.lake_manifest_fold
         << ",lake_fold=" << environment.lake_executable_fold
         << ",checker_fold=" << environment.lean_executable_fold
         << ",pinned_toolchain=" << environment.pinned_lean_4_27
         << ",pinned_library=" << environment.pinned_mathlib_revision << '\n'
         << "imported_declarations=Trace,Trace.trans,SituatedAlgorithm,rebase,trace_rebase_iff,"
            "generated_trace_rebase_transports_composition\n"
         << "first_return_testimony=deed_bytes:" << first.deed_bytes
         << ",deed_fold=" << first.deed_fold
         << ",produced_bytes=" << first.produced_artifact_bytes
         << ",produced_fold=" << first.produced_artifact_fold
         << ",exact=" << first.exact << '\n'
         << "native_inputs=rest_bytes:" << rest_load.bytes.value()
         << ",setup_bytes=" << setup_load.bytes.value()
         << ",source_bytes=0,retrieval_handles=0\n"
         << "continuation_fibers=before_a:15001000,after_a_generation:15001001,"
            "after_a_return:15001002,after_b_generation:15001003,"
            "after_b_return:15001004,final_rest:" << handoff.body.continuation << '\n'
         << "witness_b=open:" << generation.open_count
         << ",retained=" << generation.retained_count
         << ",minimal=" << generation.selected_witness.value()
         << ",inherited_fiber=" << generation.inherited_returned_fiber.value()
         << ",alternative=" << generation.fibers[1].identity.value()
         << ",alternative_obstruction="
         << static_cast<unsigned int>(generation.alternative_obstruction)
         << ",global_scans=" << generation.global_candidate_scans << '\n'
         << "lineage_b=inherited_passage:" << generation.inherited_passage.value()
         << ",inherited_kernel_return=" << generation.inherited_kernel_return.value()
         << ",returned_fiber=" << generation.inherited_returned_fiber.value()
         << ",passage=" << generation.passage.identity.value()
         << ",statement=" << generation.passage.statement.value()
         << ",proof=" << generation.passage.proof.value()
         << ",selected_rule=" << generation.passage.selected_rule.value() << '\n'
         << "generation_delta_b=head:" << value.generation_commit.predecessor.value() << ':'
         << value.generation_commit.successor.value() << ",morphology:"
         << value.generation_commit.admitted_tally_before << ':'
         << value.generation_commit.admitted_tally_after << '\n'
         << "return_delta_b=mathematical:"
         << value.returned_morphology.mathematical_before << ':'
         << value.returned_morphology.mathematical_after << ",codec:"
         << value.returned_morphology.codec_before << ':'
         << value.returned_morphology.codec_after << ",body:"
         << value.returned_morphology.commit.admitted_tally_before << ':'
         << value.returned_morphology.commit.admitted_tally_after << '\n'
         << "checker_b=exit:" << value.raw.exit_status
         << ",stdout_bytes=" << value.raw.stdout_bytes
         << ",stderr_bytes=" << value.raw.stderr_bytes
         << ",produced_bytes=" << value.raw.produced_artifact_bytes
         << ",declarations=" << value.typed.produced_declarations
         << ",remaining_goals=" << value.typed.remaining_goal_count
         << ",kernel=" << value.typed.kernel_boundary_crossed
         << ",calls=" << process.exterior_process_calls.value() << '\n'
         << "raw_b=source_fold:" << value.raw.source_fold
         << ",produced_fold=" << value.raw.produced_artifact_fold
         << ",passage=" << value.raw.passage.value()
         << ",source=" << value.raw.source.value() << '\n'
         << "ablation=excluded_fiber:" << value.exclusion.excluded_fiber.value()
         << ",excluded_delta=" << value.exclusion.excluded_delta.value()
         << ",production_generated="
         << (generation.obstruction == organ::theorem_production_obstruction::none)
         << ",ablated_generated=" << !value.ablation_generation_refused
         << ",ablated_source_bytes=" << value.ablation_source_bytes
         << ",obstruction="
         << static_cast<unsigned int>(value.ablated_generation.obstruction)
         << ",dependency_exact=" << value.dependency_exact << '\n'
         << "remount=first_fiber:" << value.remount.first_fiber.value()
         << ",second_fiber=" << value.remount.second_fiber.value()
         << ",both_preserved=" << value.remount.both_returns_preserved
         << ",source_replayed=" << value.remount.source_replayed << '\n'
         << "final_body=head:" << handoff.body.head
         << ",continuation=" << handoff.body.continuation
         << ",body_admitted_tally=" << handoff.body.regions[0].morphology
         << ",mathematical=" << handoff.mathematical_admitted_tally
         << ",codec=" << handoff.codec_admitted_tally
         << ",integrity=" << handoff.integrity << '\n'
         << "logical_work=read_support:" << execution.logical.read_support.value()
         << ",change_support=" << execution.logical.change_support.value()
         << ",alternatives=" << execution.logical.alternatives_retained.value()
         << ",obstructions=" << execution.logical.obstructions_retained.value()
         << ",reservations=" << execution.logical.reservations_consumed.value() << '\n'
         << "physical_telemetry=engine_time:unknown,exterior_checker_time:unknown,"
            "temperature:unknown,power:unknown,energy:unknown\n"
         << "deed_a_bundle_begin\n";
  output.write(first.deed, first.deed_bytes);
  output << "deed_a_bundle_end\n"
         << "deed_b_source_begin\n";
  output.write(value.formal.bytes, value.formal.byte_count);
  output << "deed_b_source_end\n"
         << "deed_b_conversation_begin\n";
  output.write(value.conversational.bytes, value.conversational.byte_count);
  output << "deed_b_conversation_end\n"
         << "deed_b_stdout_begin\n";
  output.write(value.raw.standard_output, value.raw.stdout_bytes);
  output << "deed_b_stdout_end\n"
         << "deed_b_stderr_begin\n";
  output.write(value.raw.standard_error, value.raw.stderr_bytes);
  output << "deed_b_stderr_end\n";
}

}  // namespace holonics::tests
