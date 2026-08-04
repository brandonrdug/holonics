#include <holonics/event/resident_dependent_theorem_production.hpp>

void forbidden_copy(
    holonics::event::resident_dependent_theorem_production& production) {
  auto duplicate = production;
  static_cast<void>(duplicate);
}
