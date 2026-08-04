#include <holonics/apparatus/theorem_rest_store_adapter.hpp>
#include <holonics/event/returned_fiber_exclusion_law.hpp>
#include <holonics/event/resident_theorem_production.hpp>

#include "r15_cases.hpp"

int main(int argc, char** argv) {
  if (argc != 2) { return 2; }
  holonics::event::theorem_production_rest_record inherited{};
  const auto load = holonics::apparatus::read_theorem_production_rest(argv[1], inherited);
  if (!load.returned() || load.developmental_source_bytes != holonics::exact::word{0}) { return 1; }
  const auto mount = holonics::tests::r15_case(inherited);
  holonics::event::theorem_production_remount_receipt production_receipt{};
  holonics::event::resident_theorem_production production{
      mount.foundation, inherited, production_receipt};
  const auto available = production.probe(mount.question, false);
  if (!production_receipt.same_body || production_receipt.source_replayed ||
      !available.available || available.source_accesses != 0) { return 3; }
  holonics::event::theorem_production_rest_record projected{};
  const auto exclusion = holonics::event::exclude_returned_theorem_fiber(inherited, projected);
  if (!exclusion.exact || exclusion.head_after != holonics::exact::word{14'001'001}) { return 4; }
  holonics::event::theorem_production_remount_receipt ablation_receipt{};
  holonics::event::resident_theorem_production ablation{
      mount.foundation, projected, ablation_receipt};
  const auto unavailable = ablation.probe(mount.question, false);
  if (!ablation_receipt.same_body || ablation_receipt.acquired_return_preserved ||
      unavailable.available || unavailable.source_accesses != 0) { return 5; }
  holonics::event::theorem_production_rest_record handoff{};
  if (!production.rest(handoff).returned ||
      handoff.integrity != holonics::event::theorem_production_rest_integrity(handoff) ||
      handoff.body.head != inherited.body.head || handoff.acquired.identity != inherited.acquired.identity) {
    return 6;
  }
  return 0;
}
