#include <holonics/receiver/resident_geometry.hpp>

void forbidden(const holonics::receiver::geometry_program& program) {
  holonics::receiver::resident_geometry owner{program};
  auto copied = owner;
  static_cast<void>(copied);
}
