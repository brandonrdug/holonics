#include <holonics/current/resident_weave.hpp>

void forbidden(const holonics::current::weave_program& program) {
  holonics::current::resident_weave owner{program};
  auto copied = owner;
  static_cast<void>(copied);
}
