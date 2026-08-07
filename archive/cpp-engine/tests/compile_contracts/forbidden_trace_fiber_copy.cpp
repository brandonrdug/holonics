#include <holonics/event/resident_trace_fiber.hpp>

void forbidden(holonics::event::resident_trace_fiber &source) {
  holonics::event::resident_trace_fiber duplicate{source};
  static_cast<void>(duplicate);
}
