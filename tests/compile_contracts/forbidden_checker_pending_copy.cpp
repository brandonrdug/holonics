#include <holonics/event/checker_pending_deed.hpp>

void copy_pending(const holonics::event::checker_pending_deed& pending) {
  auto forbidden = pending;
  static_cast<void>(forbidden);
}
