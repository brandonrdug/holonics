#include <holonics/event/resident_conditioned_organ.hpp>

void forbidden(const holonics::event::resident_conditioned_organ& source) {
  auto copied = source;
  static_cast<void>(copied);
}
