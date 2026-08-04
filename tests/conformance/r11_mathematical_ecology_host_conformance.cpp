#include <cstddef>

#include <holonics/event/resident_mathematical_ecology.hpp>

#include "r11_cases.hpp"
#include "r11_oracle.hpp"

int main() {
  const auto mount = holonics::tests::r11_case(117'117);
  const auto expected = holonics::tests::r11_oracle();
  holonics::event::resident_mathematical_ecology canonical{
      mount.canonical, mount.canonical_body_seed, mount.regions, true};
  holonics::event::resident_mathematical_ecology reordered{
      mount.reordered, mount.reordered_body_seed, mount.regions, true};
  const auto held = canonical.reconstruct(mount.held_out);
  const auto changed_order = reordered.reconstruct(mount.held_out);
  const auto mismatch = canonical.reconstruct(mount.mismatch);
  const auto unsolved = canonical.reconstruct(mount.unsolved);
  if (canonical.obstruction() != holonics::organ::mathematical_obstruction::none ||
      reordered.obstruction() != holonics::organ::mathematical_obstruction::none ||
      held.declaration_count != expected.declaration_count ||
      changed_order.declaration_count != held.declaration_count ||
      held.dependency_count != expected.dependency_count ||
      held.transport_alternatives != expected.transport_alternatives ||
      held.proof_term != holonics::exact::word{expected.proof_term} ||
      !held.proof_structurally_closed || !held.inherited_checked_example ||
      !held.goal_open || held.global_declaration_scans != 0 ||
      mismatch.obstruction != holonics::organ::mathematical_obstruction::type_mismatch ||
      unsolved.obstruction != holonics::organ::mathematical_obstruction::unsolved_goal ||
      !canonical.can_continue() || !reordered.can_continue()) {
    return 1;
  }
  for (std::size_t slot = 0; slot < expected.declaration_count; ++slot) {
    if (held.declaration_ids[slot] != holonics::exact::word{expected.declaration_ids[slot]} ||
        changed_order.declaration_ids[slot] != held.declaration_ids[slot]) {
      return 1;
    }
  }
  return 0;
}
