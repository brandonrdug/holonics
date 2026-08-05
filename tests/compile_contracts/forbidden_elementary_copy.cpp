#include <holonics/event/resident_elementary_calculus.hpp>

void forbidden(holonics::event::resident_elementary_calculus &source) {
  holonics::event::resident_elementary_calculus duplicate{source};
  static_cast<void>(duplicate);
}
