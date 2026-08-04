#include "r16_cases.hpp"

namespace holonics::tests {
namespace {

[[nodiscard]] organ::theorem_production_foundation foundation() noexcept {
  organ::theorem_production_foundation value{};
  value.ecology = exact::word{111'001};
  value.trace_declaration = exact::word{112'001};
  value.trace_trans_declaration = exact::word{112'033};
  value.rebase_declaration = exact::word{112'015};
  value.trace_rebase_declaration = exact::word{112'023};
  value.provenance = exact::word{111'106};
  value.rules[0] = {exact::word{141'010}, exact::word{141'011},
      organ::theorem_formation::compose_then_transport, 3};
  value.rules[1] = {exact::word{141'020}, exact::word{141'021},
      organ::theorem_formation::transport_then_compose, 4};
  return value;
}

}  // namespace

apparatus::terminal_theorem_mount r16_case(
    const event::theorem_production_rest_record& inherited,
    const event::dependent_theorem_setup& setup) noexcept {
  return {foundation(), inherited, setup};
}

event::theorem_production_rest_record r16_host_rest() noexcept {
  event::theorem_production_rest_record record{};
  record.body.head = 14'001'002;
  record.body.next_head = 14'001'003;
  record.body.continuation = 15'001'002;
  record.body.next_continuation = 15'001'003;
  record.body.lineage = 16'001'002;
  record.body.regions[0] = {140, 171'200};
  record.body.regions[1] = {129, 0};
  record.body.regions[2] = {130, 0};
  record.body.regions[3] = {131, 0};
  record.body.integrity = body::rest_integrity(record.body);
  record.acquired = {exact::word{181'200}, exact::word{171'200},
      exact::word{151'200}, exact::word{161'200}, exact::word{160'200},
      exact::word{141'010}, exact::word{5}, 3, true};
  record.mathematical_morphology = 46;
  record.codec_morphology = 34;
  record.integrity = event::theorem_production_rest_integrity(record);
  return record;
}

event::dependent_theorem_setup r16_host_setup() noexcept {
  event::dependent_theorem_setup setup{};
  setup.question = {exact::word{142'200}, exact::word{142'201},
      exact::word{181'200}, exact::word{142'202}, 3};
  setup.statement = exact::word{152'200};
  setup.proof = exact::word{162'200};
  setup.passage = exact::word{172'200};
  setup.selected_route = exact::word{182'200};
  setup.predicted_consequence = exact::word{192'200};
  setup.dependency_count = 2;
  setup.frozen = true;
  setup.complete_source_absent = true;
  setup.factors_through_returned_fiber = true;
  setup.integrity = event::dependent_setup_integrity(setup);
  return setup;
}

}  // namespace holonics::tests
