#include <holonics/event/resident_geometry_inquiry.hpp>

void forbidden_copy(holonics::event::resident_geometry_inquiry& production) {
  auto duplicate = production;
  static_cast<void>(duplicate);
}
