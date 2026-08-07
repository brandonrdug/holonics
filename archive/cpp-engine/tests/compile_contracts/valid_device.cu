#include <concepts>

#include <holonics/apparatus/resident_world_contract.hpp>
#include <holonics/body/ownership.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/deed.hpp>
#include <holonics/exact/word.hpp>
#include <holonics/structure/occurrence.hpp>

using device_carrier = holonics::exact::word;
using device_port = holonics::structure::port<
    device_carrier,
    holonics::structure::port_direction::inbound>;
using device_occurrence = holonics::structure::occurrence<device_carrier, device_port>;

static_assert(holonics::exact::exact_carrier<device_carrier>);
static_assert(holonics::structure::typed_port<device_port>);
static_assert(holonics::structure::situated_occurrence<device_occurrence>);
static_assert(holonics::body::continuation<holonics::body::continuation_capability>);
static_assert(holonics::event::pending_deed<holonics::event::pending_contract>);
static_assert(holonics::event::delta<holonics::event::delta_contract>);
static_assert(!std::copy_constructible<holonics::apparatus::resident_world_contract>);

extern "C" __global__ void r0_contract_probe() {}
