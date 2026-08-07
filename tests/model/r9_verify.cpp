#include "r9_verify.hpp"

namespace holonics::tests {
namespace {
[[nodiscard]] std::size_t crossing_failures(
    const codec::codec_crossing& crossing,
    codec::crossing_kind kind,
    std::uint64_t occurrence,
    std::uint64_t lineage) noexcept {
  return crossing.kind != kind || crossing.obstruction != codec::codec_obstruction::none ||
      crossing.occurrence != exact::word{occurrence} ||
      crossing.lineage != exact::word{lineage} ||
      crossing.program.value() == 0 || crossing.version.value() == 0 ||
      crossing.source_face.value() == 0 || crossing.target_face.value() == 0 ||
      crossing.core_occurrence.value() == 0;
}

}  // namespace

std::size_t r9_verification_failures(
    const apparatus::reflective_codec_executor_receipt& execution,
    const apparatus::reflective_codec_observation& actual,
    const r9_expected& expected) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned();
  failures += execution.kernel_launches != exact::word{4};
  failures += execution.launched_threads != exact::word{4};
  failures += execution.host_semantic_events != exact::word{0};
  failures += actual.obstruction != codec::codec_obstruction::none;
  failures += crossing_failures(actual.before.parsed, codec::crossing_kind::parse, 90'100U, 90'200U);
  failures += crossing_failures(actual.before.rendered, codec::crossing_kind::render, 90'101U, 90'201U);
  failures += crossing_failures(actual.before.transduced, codec::crossing_kind::transduce, 90'102U, 90'202U);
  failures += crossing_failures(actual.before.unrelated_parsed, codec::crossing_kind::parse, 90'103U, 90'203U);
  failures += actual.before.parsed.predecessor != exact::word{expected.predecessor} ||
      actual.before.parsed.program != exact::word{expected.operative} ||
      actual.before.unrelated_parsed.program != exact::word{expected.unrelated} ||
      actual.before.parsed.core_occurrence != exact::word{expected.core_occurrence} ||
      actual.before.parsed.core_value != exact::word{expected.before_core} ||
      actual.before.rendered.output.first != exact::word{expected.before_render_first} ||
      actual.before.transduced.output.first != exact::word{expected.before_transduce_first} ||
      actual.before.transduced.output.second != exact::word{expected.before_transduce_second} ||
      actual.before.unrelated_parsed.core_value != exact::word{expected.before_core};
  failures += actual.reflection.obstruction != codec::codec_obstruction::none ||
      actual.reflection.environment != exact::word{expected.environment} ||
      actual.reflection.inherited_provenance != exact::word{expected.provenance} ||
      actual.reflection.operative.identity != exact::word{expected.operative} ||
      actual.reflection.operative.version != exact::word{1} ||
      actual.reflection.continuation.body_head != exact::word{expected.predecessor} ||
      actual.reflection.continuation.pending_serial != exact::word{expected.continuation} ||
      !actual.reflection.continuation.pending ||
      !actual.reflection.continuation.reified_view_only ||
      actual.reflection.environment_cloned || actual.reflection.continuation_cloned;
  failures += actual.revision.obstruction != codec::codec_obstruction::none ||
      actual.revision.predecessor != exact::word{expected.predecessor} ||
      actual.revision.successor != exact::word{expected.successor} ||
      actual.revision.old_version != exact::word{1} || actual.revision.new_version != exact::word{2} ||
      actual.revision.old_bias != exact::word{2} || actual.revision.new_bias != exact::word{5} ||
      !actual.revision.same_continuation || !actual.revision.law_changed ||
      !actual.revision.committed;
  failures += actual.rest.obstruction != codec::codec_obstruction::none ||
      !actual.rest.body.returned || !actual.rest.source_detached ||
      actual.rest.program != exact::word{expected.operative} || actual.rest.version != exact::word{2};
  failures += actual.remount.obstruction != codec::codec_obstruction::none ||
      !actual.remount.body.returned || !actual.remount.same_body || actual.remount.source_replayed ||
      actual.remount.program != exact::word{expected.operative} ||
      actual.remount.version != exact::word{2};
  failures += crossing_failures(actual.after.parsed, codec::crossing_kind::parse, 90'300U, 90'400U);
  failures += crossing_failures(actual.after.rendered, codec::crossing_kind::render, 90'301U, 90'401U);
  failures += crossing_failures(actual.after.transduced, codec::crossing_kind::transduce, 90'302U, 90'402U);
  failures += crossing_failures(actual.after.unrelated_parsed, codec::crossing_kind::parse, 90'303U, 90'403U);
  failures += actual.after.parsed.core_value != exact::word{expected.after_core} ||
      actual.after.rendered.output.first != exact::word{expected.after_render_first} ||
      actual.after.transduced.output.first != exact::word{expected.after_transduce_first} ||
      actual.after.transduced.output.second != exact::word{expected.after_transduce_second} ||
      actual.after.unrelated_parsed.core_value != exact::word{expected.after_core};
  failures += actual.final_head != exact::word{expected.successor} ||
      actual.final_region.current != expected.current;
  failures += !actual.storage_semantics_invariant || !actual.source_detached ||
      !actual.reflection_exact || !actual.revision_changed_conduct ||
      !actual.same_body_remounted || !actual.syntax_not_core_identity ||
      !actual.local_law_without_registry;
  return failures;
}

}  // namespace holonics::tests
