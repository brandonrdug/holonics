#include <holonics/event/resident_expression_geometry.hpp>

void forbidden(holonics::event::resident_expression_geometry& owner) {
  auto copied = owner;
  static_cast<void>(copied);
}
