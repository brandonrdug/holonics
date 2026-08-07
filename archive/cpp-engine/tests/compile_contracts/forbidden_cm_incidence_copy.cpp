#include <holonics/event/resident_cm_incidence.hpp>

void forbidden_copy(const holonics::event::resident_cm_incidence& source) {
  holonics::event::resident_cm_incidence copy{source};
  static_cast<void>(copy);
}
