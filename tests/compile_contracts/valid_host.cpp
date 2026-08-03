#include <concepts>
#include <type_traits>

#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/apparatus/resident_world_contract.hpp>
#include <holonics/body/ownership.hpp>
#include <holonics/codec/environment_contract.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/deed.hpp>
#include <holonics/event/obstruction.hpp>
#include <holonics/exact/word.hpp>
#include <holonics/organ/constitutive_contract.hpp>
#include <holonics/receiver/chart_contract.hpp>
#include <holonics/structure/occurrence.hpp>

namespace {

using carrier = holonics::exact::word;
using inbound_port = holonics::structure::port<
    carrier,
    holonics::structure::port_direction::inbound>;
using outbound_port = holonics::structure::port<
    carrier,
    holonics::structure::port_direction::outbound>;
using occurrence = holonics::structure::occurrence<carrier, inbound_port>;
using organ = holonics::organ::constitutive_contract<inbound_port, outbound_port>;

static_assert(holonics::exact::exact_carrier<carrier>);
static_assert(holonics::structure::typed_port<inbound_port>);
static_assert(holonics::structure::situated_occurrence<occurrence>);
static_assert(holonics::body::continuation<holonics::body::continuation_capability>);
static_assert(holonics::event::pending_deed<holonics::event::pending_contract>);
static_assert(holonics::event::delta<holonics::event::delta_contract>);
static_assert(holonics::event::obstruction<holonics::event::open_obstruction>);
static_assert(holonics::structure::receipt<holonics::current::logical_resource_receipt>);
static_assert(holonics::structure::receipt<holonics::apparatus::physical_telemetry_receipt>);
static_assert(!std::same_as<
              holonics::current::logical_resource_receipt,
              holonics::apparatus::physical_telemetry_receipt>);
static_assert(std::same_as<typename organ::input_port_type, inbound_port>);
static_assert(!std::copy_constructible<holonics::body::body_contract>);
static_assert(!std::is_copy_assignable_v<holonics::body::body_contract>);
static_assert(!std::copy_constructible<holonics::body::live_morphology_contract>);
static_assert(!std::is_copy_assignable_v<holonics::body::live_morphology_contract>);
static_assert(!std::copy_constructible<holonics::body::rest_ownership>);
static_assert(!std::is_copy_assignable_v<holonics::body::rest_ownership>);
static_assert(!std::copy_constructible<holonics::codec::environment_contract>);
static_assert(!std::is_copy_assignable_v<holonics::codec::environment_contract>);
static_assert(!std::copy_constructible<holonics::apparatus::resident_world_contract>);
static_assert(!std::is_copy_assignable_v<holonics::apparatus::resident_world_contract>);

}  // namespace

int main() { return 0; }
