#include <type_traits>

#include <holonics/current/current_law.hpp>
#include <holonics/current/resident_causal_body.hpp>

#include "../model/r5_cases.hpp"
#include "../model/r5_oracle.hpp"

static_assert(!std::is_copy_constructible_v<holonics::current::resident_causal_body>);
static_assert(!std::is_move_constructible_v<holonics::current::resident_causal_body>);
static_assert(!std::is_copy_constructible_v<holonics::current::frontier_pending>);

int main() {
  const auto mount = holonics::tests::r5_cases();
  for (std::size_t slot = 0; slot < mount.count; ++slot) {
    if (holonics::current::validate_program(mount.programs[slot]) !=
        holonics::current::current_obstruction::none) {
      return 1;
    }
  }
  const auto oracle = holonics::tests::r5_oracle(mount);
  if (oracle.cases[0].state != holonics::current::current_status::exact_rest ||
      oracle.cases[0].front_count != 4 || !oracle.cases[0].compositional_quiescence ||
      oracle.cases[1].state != holonics::current::current_status::exact_rest ||
      oracle.cases[1].front_count != 2 || !oracle.cases[1].compositional_quiescence ||
      oracle.cases[2].state != holonics::current::current_status::open_frontier ||
      oracle.cases[2].final_currents[0].local_state != holonics::exact::word{18} ||
      oracle.cases[3].obstruction != holonics::current::current_obstruction::arithmetic_overflow ||
      oracle.cases[3].successor != oracle.cases[3].predecessor) {
    return 2;
  }
  return 0;
}
