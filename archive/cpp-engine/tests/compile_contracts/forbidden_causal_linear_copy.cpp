#include <holonics/event/resident_causal_linear.hpp>

void forbidden_copy(const holonics::event::resident_causal_linear& source) {
  holonics::event::resident_causal_linear copy{source};
  static_cast<void>(copy);
}
