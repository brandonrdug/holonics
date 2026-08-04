#include "r14_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r14_artifact(std::ostream& output,
    const apparatus::theorem_production_executor_receipt& execution,
    const event::theorem_production_observation& value,
    const event::theorem_production_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& generation = value.generation;
  const auto& process = execution.process;
  const auto& environment = process.environment;
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r14_first_theorem_production.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "engine_source_reads=" << execution.engine_source_reads.value() << '\n'
         << "verification_failures=" << failures << '\n'
         << "environment=toolchain_fold:" << environment.toolchain_fold
         << ",manifest_fold=" << environment.lake_manifest_fold
         << ",lake_fold=" << environment.lake_executable_fold
         << ",checker_fold=" << environment.lean_executable_fold
         << ",pinned_toolchain=" << environment.pinned_lean_4_27
         << ",pinned_library=" << environment.pinned_mathlib_revision << '\n'
         << "question=identity:" << generation.expansion.goal.identity.value()
         << ",receiver=" << generation.expansion.goal.receiver.value()
         << ",maximum_dependencies=" << generation.expansion.goal.maximum_dependencies << '\n'
         << "alternatives=open:" << generation.expansion.open_count
         << ",retained=" << generation.expansion.retained_count
         << ",dependencies=" << generation.expansion.fibers[0].dependency_count << ':'
         << generation.expansion.fibers[1].dependency_count
         << ",global_scans=" << generation.expansion.global_candidate_scans << '\n'
         << "passage=identity:" << generation.passage.identity.value()
         << ",statement=" << generation.passage.statement.value()
         << ",proof=" << generation.passage.proof.value()
         << ",rule=" << generation.passage.selected_rule.value()
         << ",lineage=" << generation.passage.lineage.value() << '\n'
         << "generation_delta=head:" << value.generation_commit.predecessor.value() << ':'
         << value.generation_commit.successor.value() << ",morphology:"
         << value.generation_commit.morphology_before << ':'
         << value.generation_commit.morphology_after << '\n'
         << "exclusion=answer_matches:" << generation.exclusion.mounted_answer_matches
         << ",lookups=" << generation.exclusion.lookup_entries
         << ",quoted_bytes=" << generation.exclusion.quoted_source_bytes
         << ",references=" << generation.exclusion.reference_calls
         << ",retained_source_bytes=" << generation.exclusion.retained_development_source_bytes
         << ",target_absent=" << generation.exclusion.target_absent_at_mount
         << ",source_detached=" << generation.exclusion.source_detached_at_rest << '\n'
         << "checker=exit:" << value.raw.exit_status
         << ",stdout_bytes=" << value.raw.stdout_bytes
         << ",stderr_bytes=" << value.raw.stderr_bytes
         << ",produced_bytes=" << value.raw.produced_artifact_bytes
         << ",declarations=" << value.typed.produced_declarations
         << ",remaining_goals=" << value.typed.remaining_goal_count
         << ",kernel=" << value.typed.kernel_boundary_crossed
         << ",calls=" << process.exterior_process_calls.value() << '\n'
         << "raw=source_fold:" << value.raw.source_fold
         << ",produced_fold=" << value.raw.produced_artifact_fold
         << ",passage=" << value.raw.passage.value()
         << ",source=" << value.raw.source.value() << '\n'
         << "pending=predecessor:" << value.outbound.predecessor.value()
         << ",event=" << value.outbound.event.value()
         << ",occurrence=" << value.outbound.occurrence.value()
         << ",before=" << value.pending_before_process
         << ",after=" << value.pending_after_return << '\n'
         << "return_delta=mathematical:" << value.returned_morphology.mathematical_before << ':'
         << value.returned_morphology.mathematical_after << ",codec:"
         << value.returned_morphology.codec_before << ':'
         << value.returned_morphology.codec_after << ",body:"
         << value.returned_morphology.commit.morphology_before << ':'
         << value.returned_morphology.commit.morphology_after << '\n'
         << "behavior=before_available:" << value.before.available
         << ",after_available=" << value.after.available
         << ",changed=" << value.behavior_changed
         << ",used_fiber=" << value.after.used_returned_fiber.value() << '\n'
         << "rest=head:" << handoff.body.head << ",continuation=" << handoff.body.continuation
         << ",integrity=" << handoff.integrity
         << ",source_replayed=" << value.remount.source_replayed << '\n'
         << "ablation=excluded_delta:" << value.ablation.excluded_delta.value()
         << ",excluded_fiber=" << value.ablation.excluded_fiber.value()
         << ",production_available=" << value.ablation.production.available
         << ",ablated_available=" << value.ablation.ablated.available
         << ",consequence_lost=" << value.ablation.consequence_lost << '\n'
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
