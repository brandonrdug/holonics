#include <holonics/event/resident_arithmetic_spectral.hpp>

void forbidden(holonics::event::resident_arithmetic_spectral& source) {
  holonics::event::resident_arithmetic_spectral copied{source};
  static_cast<void>(copied);
}
