#include "r10_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {
void write_probe(std::ostream& output, const char* label,
    const receiver::conditioning_probe_receipt& probe) noexcept {
  output << label << "=question:" << probe.question.identity.value()
         << ",receiver=" << probe.question.receiver.value()
         << ",head=" << probe.body_head.value() << ",organ=" << probe.organ.value()
         << ",weight=" << probe.morphology_response_weight.value()
         << ",response=" << probe.consequence.response.value()
         << ",incidence=" << probe.consequence.incidence.value()
         << ",transport=" << probe.consequence.transport.value()
         << ",codec=" << probe.consequence.codec.value()
         << ",obstruction=" << probe.consequence.obstruction.value()
         << ",consumed=" << probe.live_body_consumed
         << ",cloned=" << probe.live_body_cloned << '\n';
}
}  // namespace

void write_r10_artifact(std::ostream& output,
    const apparatus::conditioning_executor_receipt& execution,
    const apparatus::conditioning_observation& value,
    std::size_t failures) noexcept {
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r10_conditioning_native_morphology.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "passage_bytes_after_training=" << execution.passage_bytes_after_training.value() << '\n'
         << "host_semantic_events=" << execution.host_semantic_events.value() << '\n'
         << "behavior_changed=" << value.behavior_changed << '\n'
         << "final_continuation_valid=" << value.final_continuation_valid << '\n'
         << "verification_failures=" << failures << '\n'
         << "mount=organ:" << value.mounting.organ.value()
         << ",provenance=" << value.mounting.provenance.value()
         << ",inherited=" << value.mounting.inherited
         << ",changed=" << value.mounting.conduct_changed << '\n';
  write_probe(output, "before", value.before);
  output << "exposure=occurrence:" << value.exposure.occurrence.occurrence.value()
         << ",source=" << value.exposure.occurrence.source_identity.value()
         << ",response=" << value.exposure.received.response.value()
         << ",crossing=" << value.exposure.crossing_material
         << ",morphology_changed=" << value.exposure.morphology_changed
         << ",source_retained=" << value.exposure.source_retained << '\n'
         << "reference=occurrence:" << value.reference.occurrence.occurrence.value()
         << ",testimony=" << value.reference.consulted.response.value()
         << ",separate=" << value.reference.separately_retained_testimony
         << ",applied=" << value.reference.applied_to_morphology << '\n';
  const auto& training = value.training;
  output << "training=occurrence:" << training.returned.occurrence.value()
         << ",head=" << training.predecessor.value() << ':' << training.successor.value()
         << ",continuation=" << training.continuation.value()
         << ",weight=" << training.before.response_weight.value() << ':'
         << training.after.response_weight.value()
         << ",transport=" << training.before.transport_weight.value() << ':'
         << training.after.transport_weight.value()
         << ",incidence=" << training.before.incidence_gate.value() << ':'
         << training.after.incidence_gate.value()
         << ",codec=" << training.before.codec_bias.value() << ':'
         << training.after.codec_bias.value()
         << ",threshold=" << training.before.obstruction_threshold.value() << ':'
         << training.after.obstruction_threshold.value()
         << ",founded_by_return=" << training.founded_by_return
         << ",count_threshold=" << training.count_threshold_used
         << ",committed=" << training.committed << '\n';
  const auto& access = value.source_access;
  output << "source_access=bytes:" << access.retained_source_bytes.value()
         << ",lookup=" << access.lookup_entries.value()
         << ",after=" << access.source_accesses_after_training.value()
         << ",lossless=" << access.lossless_corpus_encoding
         << ",native=" << access.reusable_native_morphology
         << ",detached=" << access.source_detached << '\n'
         << "remount=head:" << value.remount.body.head.value()
         << ",same_body=" << value.remount.same_body
         << ",source_replayed=" << value.remount.source_replayed << '\n';
  write_probe(output, "after", value.after);
  output << "ablation=production:" << value.ablation.production_body.value()
         << ",experimental=" << value.ablation.ablation_body.value()
         << ",response=" << value.ablation.production.consequence.response.value() << ':'
         << value.ablation.ablated.consequence.response.value()
         << ",separate=" << value.ablation.separately_founded
         << ",cloned=" << value.ablation.owner_cloned
         << ",lost=" << value.ablation.consequence_lost << '\n'
         << "successor=head:" << value.final_head.value()
         << ",
}

}  // namespace holonics::tests
