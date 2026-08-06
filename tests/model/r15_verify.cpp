#include "r15_verify.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] bool same_rest(const event::theorem_production_rest_record& left,
    const event::theorem_production_rest_record& right) noexcept {
  const auto* a = reinterpret_cast<const unsigned char*>(&left);
  const auto* b = reinterpret_cast<const unsigned char*>(&right);
  for (std::size_t slot = 0; slot < sizeof(left); ++slot) {
    if (a[slot] != b[slot]) { return false; }
  }
  return true;
}

}  // namespace

std::size_t r15_verification_failures(
    const apparatus::theorem_rest_store_receipt& load,
    const apparatus::return_conditioning_mount& mount,
    const apparatus::return_conditioning_executor_receipt& execution,
    const event::return_conditioning_observation& actual,
    const event::theorem_production_rest_record& handoff,
    const event::dependent_theorem_setup& setup) noexcept {
  std::size_t failures = 0;
  failures += !load.returned() || load.bytes != exact::word{sizeof(mount.inherited)} ||
      load.read_calls != exact::word{1} || load.developmental_source_bytes != exact::word{0} ||
      load.retrieval_handles != exact::word{0} || !load.integrity_exact;
  failures += !execution.returned() || execution.kernel_launches != exact::word{4} ||
      execution.launched_threads != exact::word{4} ||
      execution.host_semantic_events != exact::word{0} ||
      execution.engine_source_reads != exact::word{0} ||
      execution.exterior_retrieval_calls != exact::word{0} ||
      execution.developmental_source_bytes != exact::word{0};
  failures += !actual.production_remount.same_body ||
      !actual.production_remount.acquired_return_preserved ||
      actual.production_remount.source_replayed ||
      actual.production_head != exact::word{14'001'002} || !actual.source_detached ||
      !actual.production.available ||
      actual.production.used_returned_fiber != exact::word{181'200} ||
      actual.production.consequence != exact::word{192'200} ||
      actual.production.source_accesses != 0;
  const auto& exclusion = actual.exclusion;
  failures += exclusion.excluded_fiber != exact::word{181'200} ||
      exclusion.excluded_delta != exact::word{5} ||
      exclusion.head_before != exact::word{14'001'002} ||
      exclusion.head_after != exact::word{14'001'001} ||
      exclusion.body_admitted_tally_before != 140 || exclusion.body_admitted_tally_after != 135 ||
      exclusion.mathematical_before != 46 || exclusion.mathematical_after != 43 ||
      exclusion.codec_before != 34 || exclusion.codec_after != 32 ||
      !exclusion.original_integrity_exact || !exclusion.projected_integrity_exact ||
      !exclusion.exact;
  failures += !actual.ablation_remount.same_body ||
      actual.ablation_remount.acquired_return_preserved ||
      actual.ablation_remount.source_replayed ||
      actual.ablation_head != exact::word{14'001'001} || actual.ablated.available ||
      actual.ablated.obstruction != organ::theorem_production_obstruction::returned_fiber_absent ||
      actual.ablated.source_accesses != 0 || !actual.behavior_changed || !actual.dependency_exact;
  failures += setup.question.identity != exact::word{142'200} ||
      setup.question.receiver != exact::word{142'201} ||
      setup.question.required_returned_fiber != exact::word{181'200} ||
      setup.statement != exact::word{152'200} || setup.proof != exact::word{162'200} ||
      setup.passage != exact::word{172'200} || setup.selected_route != exact::word{182'200} ||
      setup.predicted_consequence != exact::word{192'200} || setup.dependency_count != 2 ||
      !setup.frozen || !setup.complete_source_absent ||
      !setup.factors_through_returned_fiber ||
      setup.integrity != event::dependent_setup_integrity(setup) ||
      setup.integrity != actual.setup.integrity;
  failures += !actual.handoff.returned || !actual.handoff.source_detached ||
      actual.handoff.retained_source_bytes != 0 || !actual.handoff_continuation_valid ||
      handoff.integrity != event::theorem_production_rest_integrity(handoff) ||
      !same_rest(mount.inherited, handoff);
  return failures;
}

}  // namespace holonics::tests
