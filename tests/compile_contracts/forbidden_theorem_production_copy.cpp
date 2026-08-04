#include <concepts>
#include <type_traits>

#include <holonics/event/resident_theorem_production.hpp>

static_assert(!std::copy_constructible<holonics::event::resident_theorem_production>);
static_assert(!std::is_copy_assignable_v<holonics::event::resident_theorem_production>);

int main() {
  holonics::body::rest_region regions[holonics::body::live_region_capacity]{};
  holonics::organ::theorem_production_foundation foundation{};
  holonics::event::resident_theorem_production first{foundation, 1, regions, 1, 1};
  holonics::event::resident_theorem_production forbidden{first};
  return forbidden.can_continue() ? 0 : 1;
}
