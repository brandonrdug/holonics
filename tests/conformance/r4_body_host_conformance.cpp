#include <cstddef>
#include <cstdint>
#include <new>

#include <holonics/event/lifecycle_law.hpp>

int main() {
  holonics::body::rest_region regions[holonics::body::live_region_capacity]{};
  alignas(holonics::event::live_pending)
      unsigned char pending_storage[sizeof(holonics::event::live_pending)]{};
  alignas(holonics::event::live_delta)
      unsigned char delta_storage[sizeof(holonics::event::live_delta)]{};
  holonics::body::continuing_body standing{300'000'000U, regions};
  const auto before = holonics::event::observe(standing);
  const holonics::event::deed_request request{310'000'000U, 1, 3};
  holonics::event::outbound_occurrence outbound{};
  auto* pending = reinterpret_cast<holonics::event::live_pending*>(pending_storage);
  auto* delta = reinterpret_cast<holonics::event::live_delta*>(delta_storage);
  if (holonics::event::open(standing, request, pending, outbound) !=
      holonics::event::lifecycle_status::exact) { return 1; }
  const holonics::event::deed_return returned{outbound.predecessor, outbound.event,
      outbound.expected_return_port, outbound.lineage + 1U, 7};
  if (holonics::event::resume(*pending, returned, delta) !=
      holonics::event::lifecycle_status::exact) { return 2; }
  holonics::event::recover(standing, *delta);
  const auto after = holonics::event::observe(standing);
  if (before.head != after.head || before.continuation != after.continuation ||
      before.regions[1].morphology != after.regions[1].morphology) { return 3; }
  holonics::body::rest_record rest{};
  const auto rest_receipt = standing.rest(rest);
  rest.integrity ^= 1U;
  holonics::body::rest_receipt remount_receipt{};
  const auto remounted = holonics::body::continuing_body::remount(rest, remount_receipt);
  if (!rest_receipt.returned || remount_receipt.returned || remounted.can_open()) { return 4; }
  return 0;
}
