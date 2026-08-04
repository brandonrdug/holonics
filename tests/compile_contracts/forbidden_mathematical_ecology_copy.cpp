#include <holonics/event/resident_mathematical_ecology.hpp>

void forbidden_copy(const holonics::event::resident_mathematical_ecology& ecology) {
  auto duplicate = ecology;
  static_cast<void>(duplicate);
}
