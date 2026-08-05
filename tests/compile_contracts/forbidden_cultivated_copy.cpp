#include <holonics/event/resident_cultivated_organs.hpp>

void forbidden(const holonics::event::resident_cultivated_organs &source) {
  holonics::event::resident_cultivated_organs copy{source};
  static_cast<void>(copy);
}
