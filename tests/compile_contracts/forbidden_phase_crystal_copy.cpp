#include <holonics/event/resident_phase_crystal.hpp>

void forbidden_copy(holonics::event::resident_phase_crystal& source) {
  holonics::event::resident_phase_crystal copy{source};
  static_cast<void>(copy);
}
