#include <holonics/event/resident_algebraic_variation.hpp>

void forbidden_copy(const holonics::event::resident_algebraic_variation& source) {
  holonics::event::resident_algebraic_variation copy{source};
  static_cast<void>(copy);
}
