#include <holonics/event/resident_regular_singular.hpp>

void forbidden(holonics::event::resident_regular_singular& body) {
  holonics::event::resident_regular_singular duplicate = body;
  static_cast<void>(duplicate);
}
