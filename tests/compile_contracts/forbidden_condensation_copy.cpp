#include <holonics/event/resident_condensation.hpp>

void forbidden(const holonics::receiver::condensation_program& program,
    const holonics::body::rest_region* regions) {
  holonics::event::resident_condensation owner{program, regions};
  auto copied = owner;
  static_cast<void>(copied);
}
