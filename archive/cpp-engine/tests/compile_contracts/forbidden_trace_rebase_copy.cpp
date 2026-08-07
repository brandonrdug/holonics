#include <holonics/event/resident_trace_rebase.hpp>

void forbidden(holonics::event::resident_trace_rebase &source) {
  holonics::event::resident_trace_rebase duplicate{source};
  static_cast<void>(duplicate);
}
