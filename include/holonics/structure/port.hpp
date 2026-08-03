#pragma once

#include <concepts>

#include <holonics/structure/identity.hpp>

namespace holonics::structure {

enum class port_direction : unsigned char { inbound, outbound };

struct port_identity_owner final {};
struct boundary_identity_owner final {};

struct typed_port_marker final {};

template<class Port>
concept typed_port = requires {
  typename Port::holonics_typed_port;
  typename Port::carrier_type;
  typename Port::boundary_type;
  { Port::direction } -> std::convertible_to<port_direction>;
} && std::same_as<typename Port::holonics_typed_port, typed_port_marker>;

template<class Carrier, port_direction Direction>
struct port final {
  using holonics_typed_port = typed_port_marker;
  using carrier_type = Carrier;
  using boundary_type = identity<boundary_identity_owner>;
  using identity_type = identity<port_identity_owner>;

  static constexpr port_direction direction = Direction;
};

}  // namespace holonics::structure
