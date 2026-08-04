#include <holonics/event/resident_generative_math_current.hpp>

void forbidden_copy(const holonics::event::resident_generative_math_current& current) {
  auto duplicate = current;
  static_cast<void>(duplicate);
}
