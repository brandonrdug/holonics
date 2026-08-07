#include <holonics/event/resident_reflective_codec.hpp>

void forbidden(const holonics::event::resident_reflective_codec& source) {
  auto copied = source;
  static_cast<void>(copied);
}
