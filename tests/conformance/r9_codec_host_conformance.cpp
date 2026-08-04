#include <holonics/apparatus/codec_store_adapter.hpp>
#include <holonics/event/resident_reflective_codec.hpp>

#include "r9_cases.hpp"
#include "r9_oracle.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 3) { return 2; }
  auto original = holonics::apparatus::mount_codec_store(arguments[1]);
  auto relocated = holonics::apparatus::mount_relocated_codec_store(arguments[1], arguments[2]);
  if (original.receipt.state != holonics::apparatus::codec_store_status::exact ||
      relocated.receipt.state != holonics::apparatus::codec_store_status::exact ||
      !holonics::apparatus::same_codec_material(original.environment, relocated.environment)) {
    return 1;
  }
  const auto mount = holonics::tests::r9_case(
      original.environment.value(), original.receipt, relocated.receipt);
  original.environment.detach();
  relocated.environment.detach();
  holonics::event::resident_reflective_codec live{
      mount.environment, mount.body_seed, mount.regions, true};
  const auto before = live.behavior(mount.deed.probe, mount.deed.render_core, 90'100U, 90'200U);
  const auto reflection = live.reflect(
      mount.deed.reflection_occurrence, mount.deed.reflection_lineage);
  const auto revision = live.apply_revision(mount.deed.revision, reflection, mount.deed.probe);
  holonics::event::reflective_codec_rest_record record{};
  const auto rest = live.rest(record);
  holonics::event::reflective_codec_remount_receipt remount_receipt{};
  holonics::event::resident_reflective_codec remounted{record, remount_receipt};
  const auto after = remounted.behavior(
      mount.deed.probe, mount.deed.render_core, 90'300U, 90'400U);
  const auto expected = holonics::tests::r9_oracle();
  if (live.obstruction() != holonics::codec::codec_obstruction::none ||
      before.parsed.core_value != holonics::exact::word{expected.before_core} ||
      before.rendered.output.first != holonics::exact::word{expected.before_render_first} ||
      before.transduced.output.first != holonics::exact::word{expected.before_transduce_first} ||
      before.transduced.output.second != holonics::exact::word{expected.before_transduce_second} ||
      before.unrelated_parsed.core_value != before.parsed.core_value ||
      reflection.continuation.pending_serial != holonics::exact::word{expected.continuation} ||
      reflection.environment_cloned || reflection.continuation_cloned ||
      !revision.committed || !revision.same_continuation || !revision.law_changed ||
      rest.obstruction != holonics::codec::codec_obstruction::none || !rest.source_detached ||
      remount_receipt.obstruction != holonics::codec::codec_obstruction::none ||
      !remount_receipt.same_body || remount_receipt.source_replayed ||
      after.parsed.core_value != holonics::exact::word{expected.after_core} ||
      after.rendered.output.first != holonics::exact::word{expected.after_render_first} ||
      after.transduced.output.second != holonics::exact::word{expected.after_transduce_second} ||
      remounted.head() != holonics::exact::word{expected.successor} ||
      remounted.region(0).morphology != expected.morphology ||
      remounted.region(0).current != expected.current) {
    return 1;
  }
  return 0;
}
