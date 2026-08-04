#include "r10_verify.hpp"

namespace holonics::tests {

std::size_t r10_verification_failures(
    const apparatus::conditioning_executor_receipt& execution,
    const apparatus::conditioning_observation& actual,
    const r10_expected& expected) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned() || execution.kernel_launches != exact::word{6} ||
      execution.launched_threads != exact::word{6} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.passage_bytes_after_training != exact::word{0};
  failures += actual.obstruction != organ::conditioning_obstruction::none;
  failures += actual.mounting.organ != exact::word{10'001} || !actual.mounting.inherited ||
      actual.mounting.conduct_changed ||
      actual.mounting.before.response_weight != actual.mounting.after.response_weight;
  failures += actual.before.body_head != exact::word{expected.predecessor} ||
      actual.before.consequence.response != exact::word{expected.before_response} ||
      actual.before.consequence.incidence != exact::word{0} ||
      actual.before.consequence.transport != exact::word{2} ||
      actual.before.consequence.codec != exact::word{0} ||
      actual.before.consequence.obstruction != exact::word{expected.before_obstruction} ||
      actual.before.live_body_consumed || actual.before.live_body_cloned;
  failures += !actual.exposure.crossing_material || actual.exposure.morphology_changed ||
      actual.exposure.source_retained ||
      actual.exposure.received.response != exact::word{expected.exposure_response} ||
      actual.exposure.before.response_weight != actual.exposure.after.response_weight;
  failures += !actual.reference.separately_retained_testimony ||
      actual.reference.applied_to_morphology ||
      actual.reference.consulted.response != exact::word{777};
  failures += actual.training.obstruction != organ::conditioning_obstruction::none ||
      actual.training.predecessor != exact::word{expected.predecessor} ||
      actual.training.successor != exact::word{expected.successor} ||
      actual.training.continuation != exact::word{expected.continuation} ||
      actual.training.delta.response_weight != exact::word{1} ||
      actual.training.delta.transport_weight != exact::word{1} ||
      actual.training.delta.incidence_gate != exact::word{1} ||
      actual.training.delta.codec_bias != exact::word{1} ||
      actual.training.delta.obstruction_threshold != exact::word{2} ||
      !actual.training.founded_by_return || actual.training.count_threshold_used ||
      !actual.training.committed;
  failures += actual.source_access.retained_source_bytes != exact::word{0} ||
      actual.source_access.lookup_entries != exact::word{0} ||
      actual.source_access.source_accesses_after_training != exact::word{0} ||
      actual.source_access.lossless_corpus_encoding ||
      !actual.source_access.reusable_native_morphology || !actual.source_access.source_detached;
  failures += actual.rest.obstruction != organ::conditioning_obstruction::none ||
      !actual.rest.body.returned || !actual.rest.source_detached ||
      actual.remount.obstruction != organ::conditioning_obstruction::none ||
      !actual.remount.body.returned || !actual.remount.same_body || actual.remount.source_replayed;
  failures += actual.after.body_head != exact::word{expected.successor} ||
      actual.after.consequence.response != exact::word{expected.after_response} ||
      actual.after.consequence.incidence != exact::word{1} ||
      actual.after.consequence.transport != exact::word{expected.after_transport} ||
      actual.after.consequence.codec != exact::word{expected.after_codec} ||
      actual.after.consequence.obstruction != exact::word{0} ||
      actual.after.live_body_consumed || actual.after.live_body_cloned;
  failures += actual.ablation.ablation_body != exact::word{expected.ablation_body} ||
      actual.ablation.production_body == actual.ablation.ablation_body ||
      !actual.ablation.separately_founded || actual.ablation.owner_cloned ||
      !actual.ablation.consequence_lost ||
      actual.ablation.ablated.consequence.response != exact::word{expected.before_response} ||
      actual.ablation.ablated.consequence.obstruction != exact::word{expected.before_obstruction};
  failures += !actual.behavior_changed || !actual.final_continuation_valid ||
      actual.final_head != exact::word{expected.successor} ||
      actual.final_region.morphology != expected.region_morphology ||
      actual.final_region.current != expected.region_current;
  return failures;
}

}  // namespace holonics::tests
