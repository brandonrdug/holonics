#include <holonics/current/resident_causal_body.hpp>

void forbidden(const holonics::current::causal_program& program) {
  holonics::current::resident_causal_body owner{program};
  auto copied = owner;
  static_cast<void>(copied);
}
