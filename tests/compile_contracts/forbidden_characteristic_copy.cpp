#include <holonics/event/resident_characteristic.hpp>

void forbidden_copy(holonics::event::resident_characteristic& source) {
  holonics::event::resident_characteristic copy{source};
  static_cast<void>(copy);
}
