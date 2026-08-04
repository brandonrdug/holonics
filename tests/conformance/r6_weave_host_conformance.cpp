#include <type_traits>

#include <holonics/current/resident_weave.hpp>

#include "../model/r6_cases.hpp"
#include "../model/r6_oracle.hpp"

static_assert(!std::is_copy_constructible_v<holonics::current::resident_weave>);
static_assert(!std::is_move_constructible_v<holonics::current::resident_weave>);

int main() {
  const auto mount = holonics::tests::r6_cases();
  for (std::size_t slot = 0; slot < mount.count; ++slot) {
    const auto& program = mount.programs[slot];
    if (holonics::current::validate_weave_program(program) !=
        holonics::current::weave_obstruction::none ||
        !holonics::current::make_interchange(program, 2, 3).complete_successor_equal ||
        !holonics::current::make_higher_coherence(program, 4, 5, 6)
            .complete_successors_equal ||
        !holonics::current::make_interaction(program).equalized) {
      return 1;
    }
  }
  const auto oracle = holonics::tests::r6_oracle(mount);
  if (!oracle.cases[0].semantic.resource.morphology_changed ||
      oracle.cases[0].semantic.resource.remained_open ||
      !oracle.cases[1].semantic.resource.remained_open ||
      oracle.cases[1].semantic.resource.retry_count != 0) {
    return 2;
  }
  return 0;
}
