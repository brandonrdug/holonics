#include <holonics/event/resident_intrinsic_hypergeometry.hpp>

void forbidden(holonics::event::resident_intrinsic_hypergeometry& body) {
  auto duplicate = body;
  static_cast<void>(duplicate);
}
