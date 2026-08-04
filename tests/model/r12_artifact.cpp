#include "r12_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r12_artifact(std::ostream& output,
    const apparatus::generative_math_executor_receipt& execution,
    const apparatus::generative_math_observation& value,
    std::size_t failures) noexcept {
  const auto& returned = value.returned;
  const auto& generation = returned.generation;
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r12_generative_mathematical_current.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "mounted_answer_bytes=" << execution.mounted_answer_bytes.value() << '\n'
         << "external_checker_calls=" << execution.external_checker_calls.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "verification_failures=" << failures << '\n'
         << "expansion=question:" << generation.expansion.goal.identity.value()
         << ",open=" << generation.expansion.open_count
         << ",global_scans=" << generation.expansion.global_candidate_scans
         << ",dependencies=" << generation.expansion.fibers[0].dependency_count << ':'
         << generation.expansion.fibers[1].dependency_count
         << ",obstruction=" << static_cast<unsigned>(generation.expansion.obstruction) << '\n'
         << "selection=rule:" << generation.passage.selected_rule.value()
         << ",alternatives=" << generation.information.alternatives_before << ':'
         << generation.information.alternatives_after
         << ",score=" << generation.score_used
         << ",registry=" << generation.registry_used << '\n'
         << "passage=identity:" << generation.passage.identity.value()
         << ",statement=" << generation.passage.statement.value()
         << ",proof=" << generation.passage.proof.value()
         << ",premise=" << generation.passage.premise_declaration.value()
         << ",lineage=" << generation.passage.lineage.value()
         << ",closed=" << generation.passage.closed
         << ",generated=" << generation.passage.generated << '\n'
         << "exclusion=matches:" << generation.exclusion.mounted_answer_matches
         << ",lookups=" << generation.exclusion.lookup_entries
         << ",quoted_bytes=" << generation.exclusion.quoted_source_bytes
         << ",distinct=" << generation.exclusion.distinct_from_inherited
         << ",absent=" << generation.exclusion.absent_before_generation << '\n'
         << "information=head:" << generation.information.predecessor.value() << ':'
         << generation.information.successor.value()
         << ",continuation=" << generation.information.continuation.value()
         << ",morphology_delta=" << generation.information.morphology_delta.value()
         << ",obstruction_changed=" << generation.information.obstruction_changed_passage
         << ",receiver_indexed=" << generation.information.receiver_indexed << '\n'
         << "faces=formal:" << returned.formal.identity.value()
         << ",conversation=" << returned.conversational.identity.value()
         << ",passage=" << returned.formal.passage.value()
         << ",same=" << returned.same_closed_passage
         << ",formal_bytes=" << returned.formal.byte_count
         << ",conversation_bytes=" << returned.conversational.byte_count << '\n'
         << "formal_begin\n";
  output.write(returned.formal.bytes, returned.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(returned.conversational.bytes, returned.conversational.byte_count);
  output << "conversation_end\n";
}

}  // namespace holonics::tests
