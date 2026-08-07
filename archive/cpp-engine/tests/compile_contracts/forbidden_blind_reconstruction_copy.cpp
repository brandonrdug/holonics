#include <holonics/event/resident_blind_reconstruction.hpp>

void forbidden_copy(holonics::event::resident_blind_reconstruction& source) {
  holonics::event::resident_blind_reconstruction copy = source;
  (void)copy;
}
