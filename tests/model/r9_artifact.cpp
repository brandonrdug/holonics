#include "r9_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void write_crossing(std::ostream& output,
    const char* label,
    const codec::codec_crossing& crossing) noexcept {
  output << label << "=kind:" << static_cast<unsigned>(crossing.kind)
         << ",occurrence=" << crossing.occurrence.value()
         << ",lineage=" << crossing.lineage.value()
         << ",predecessor=" << crossing.predecessor.value()
         << ",program=" << crossing.program.value() << '/' << crossing.version.value()
         << ",faces=" << crossing.source_face.value() << ':' << crossing.target_face.value()
         << ",surface=" << crossing.input.first.value() << ':' << crossing.input.second.value()
         << "->" << crossing.output.first.value() << ':' << crossing.output.second.value()
         << ",core=" << crossing.core_occurrence.value() << '/' << crossing.core_value.value()
         << ",obstruction=" << static_cast<unsigned>(crossing.obstruction) << '\n';
}

}  // namespace

void write_r9_artifact(std::ostream& output,
    const apparatus::reflective_codec_executor_receipt& execution,
    const apparatus::reflective_codec_observation& observation,
    std::size_t failures) noexcept {
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r9_agnostic_codecs_reflection.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "storage_semantics_invariant=" << observation.storage_semantics_invariant << '\n'
         << "source_detached=" << observation.source_detached << '\n'
         << "reflection_exact=" << observation.reflection_exact << '\n'
         << "revision_changed_conduct=" << observation.revision_changed_conduct << '\n'
         << "same_body_remounted=" << observation.same_body_remounted << '\n'
         << "syntax_not_core_identity=" << observation.syntax_not_core_identity << '\n'
         << "local_law_without_registry=" << observation.local_law_without_registry << '\n'
         << "verification_failures=" << failures << '\n';
  write_crossing(output, "before_parse", observation.before.parsed);
  write_crossing(output, "before_render", observation.before.rendered);
  write_crossing(output, "before_transduce", observation.before.transduced);
  write_crossing(output, "unrelated_parse", observation.before.unrelated_parsed);
  const auto& reflection = observation.reflection;
  output << "reflection=occurrence:" << reflection.occurrence.value()
         << ",lineage=" << reflection.lineage.value()
         << ",environment=" << reflection.environment.value()
         << ",provenance=" << reflection.inherited_provenance.value()
         << ",program=" << reflection.operative.identity.value() << '/'
         << reflection.operative.version.value()
         << ",continuation=" << reflection.continuation.body_head.value() << ':'
         << reflection.continuation.pending_serial.value()
         << ",view=" << reflection.continuation.reified_view_only
         << ",environment_cloned=" << reflection.environment_cloned
         << ",continuation_cloned=" << reflection.continuation_cloned << '\n';
  const auto& revision = observation.revision;
  output << "revision=occurrence:" << revision.occurrence.value()
         << ",port=" << revision.return_port.value()
         << ",lineage=" << revision.lineage.value()
         << ",head=" << revision.predecessor.value() << ':' << revision.successor.value()
         << ",program=" << revision.reflected_program.value()
         << ",version=" << revision.old_version.value() << ':' << revision.new_version.value()
         << ",bias=" << revision.old_bias.value() << ':' << revision.new_bias.value()
         << ",same_continuation=" << revision.same_continuation
         << ",law_changed=" << revision.law_changed
         << ",committed=" << revision.committed << '\n';
  output << "rest=program:" << observation.rest.program.value() << '/'
         << observation.rest.version.value() << ",head=" << observation.rest.body.head.value()
         << ",source_detached=" << observation.rest.source_detached << '\n'
         << "remount=program:" << observation.remount.program.value() << '/'
         << observation.remount.version.value() << ",head="
         << observation.remount.body.head.value() << ",same_body="
         << observation.remount.same_body << ",source_replayed="
         << observation.remount.source_replayed << '\n';
  write_crossing(output, "after_parse", observation.after.parsed);
  write_crossing(output, "after_render", observation.after.rendered);
  write_crossing(output, "after_transduce", observation.after.transduced);
  output << "successor=head:" << observation.final_head.value()
         << ",admitted_tally=" << observation.final_region.admitted_tally
         << ",current=" << observation.final_region.current
         << ",obstruction=" << static_cast<unsigned>(observation.obstruction) << '\n';
}

}  // namespace holonics::tests
