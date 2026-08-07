#include <holonics/event/resident_toric_cycle.hpp>

void forbidden_copy(const holonics::event::resident_toric_cycle& source) {
  holonics::event::resident_toric_cycle copy{source};
  static_cast<void>(copy);
}
