#include <type_traits>

#include <holonics/event/resident_condensation.hpp>

#include "../model/r8_cases.hpp"
#include "../model/r8_oracle.hpp"

static_assert(!std::is_copy_constructible_v<holonics::event::resident_condensation>);
static_assert(!std::is_move_constructible_v<holonics::event::resident_condensation>);

int main() {
  const auto mount = holonics::tests::r8_case();
  if (holonics::receiver::validate_condensation_program(mount.program) !=
      holonics::receiver::condensation_obstruction::none) {
    return 1;
  }
  const auto oracle = holonics::tests::r8_oracle(mount).semantic;
  if (!oracle.factorized_boundary || !oracle.stateful_bisimulation ||
      !oracle.source_fiber_retained || !oracle.refinement.source_reopened ||
      oracle.history[0].response.factor_count != 3 ||
      oracle.history[2].response.factor_count != 4 ||
      oracle.successor.current != holonics::exact::word{214}) {
    return 2;
  }
  return 0;
}
