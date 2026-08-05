#include <holonics/event/resident_characteristic_hypergeometry.hpp>

void forbidden(holonics::event::resident_characteristic_hypergeometry &source) {
  holonics::event::resident_characteristic_hypergeometry duplicate{source};
  static_cast<void>(duplicate);
}
