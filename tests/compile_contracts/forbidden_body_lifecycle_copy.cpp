#include <holonics/event/lifecycle_law.hpp>

int main() {
  holonics::body::rest_region regions[holonics::body::live_region_capacity]{};
  holonics::body::continuing_body first{1, regions};
  holonics::body::continuing_body second{first};
  return second.can_open() ? 0 : 1;
}
