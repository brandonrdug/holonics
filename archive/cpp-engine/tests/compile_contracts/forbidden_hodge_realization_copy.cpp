#include <holonics/event/resident_hodge_realization.hpp>

void forbidden(holonics::event::resident_hodge_realization& resident) {
  auto duplicate = resident;
  static_cast<void>(duplicate);
}
