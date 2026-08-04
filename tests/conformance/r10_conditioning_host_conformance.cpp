#include <holonics/event/resident_conditioned_organ.hpp>

#include "r10_cases.hpp"
#include "r10_oracle.hpp"

int main() {
  const auto mount = holonics::tests::r10_case();
  const auto expected = holonics::tests::r10_oracle();
  holonics::event::resident_conditioned_organ production{
      mount.foundation.morphology, mount.foundation.production_seed,
      mount.foundation.regions, true};
  const auto mounting = production.mounting();
  const auto before = production.probe(mount.held_out);
  const auto exposure = production.expose(mount.passage.exposure);
  const auto reference = production.consult(mount.passage.reference);
  const auto training = production.train(mount.passage.training);
  holonics::event::conditioned_organ_rest_record record{};
  const auto rest = production.rest(record);
  holonics::event::conditioned_organ_remount_receipt remount_receipt{};
  holonics::event::resident_conditioned_organ remounted{record, remount_receipt};
  const auto after = remounted.probe(mount.held_out);
  holonics::event::resident_conditioned_organ ablated{
      mount.foundation.morphology, mount.foundation.ablation_seed,
      mount.foundation.regions, true};
  const auto without = ablated.probe(mount.held_out);
  if (!mounting.inherited || mounting.conduct_changed ||
      before.consequence.response != holonics::exact::word{expected.before_response} ||
      exposure.morphology_changed || exposure.source_retained ||
      !reference.separately_retained_testimony || reference.applied_to_morphology ||
      training.obstruction != holonics::organ::conditioning_obstruction::none ||
      !training.founded_by_return || training.count_threshold_used || !training.committed ||
      rest.obstruction != holonics::organ::conditioning_obstruction::none ||
      remount_receipt.obstruction != holonics::organ::conditioning_obstruction::none ||
      !remount_receipt.same_body || remount_receipt.source_replayed ||
      after.consequence.response != holonics::exact::word{expected.after_response} ||
      after.consequence.obstruction != holonics::exact::word{0} ||
      without.consequence.response != before.consequence.response ||
      without.consequence.obstruction != before.consequence.obstruction ||
      ablated.head() != holonics::exact::word{expected.ablation_body} ||
      remounted.head() != holonics::exact::word{expected.successor} ||
      !remounted.can_continue()) {
    return 1;
  }
  return 0;
}
