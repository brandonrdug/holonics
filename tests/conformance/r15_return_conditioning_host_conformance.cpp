#include <holonics/apparatus/theorem_rest_store_adapter.hpp>
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
  holonics::event::theorem_production_rest_record handoff{};
  if (!production.rest(handoff).returned ||
      handoff.integrity != holonics::event::theorem_production_rest_integrity(handoff) ||
      handoff.body.head != inherited.body.head || handoff.acquired.identity != inherited.acquired.identity) {
    return 6;
  }
  return 0;
}
