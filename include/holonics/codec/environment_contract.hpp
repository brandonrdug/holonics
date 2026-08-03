#pragma once

#include <holonics/exact/config.hpp>
#include <holonics/structure/port.hpp>

namespace holonics::codec {

class environment_contract final {
 public:
  environment_contract() = delete;
  environment_contract(const environment_contract&) = delete;
  environment_contract& operator=(const environment_contract&) = delete;
  HOLONICS_CALLABLE environment_contract(environment_contract&&) noexcept {}
  HOLONICS_CALLABLE environment_contract& operator=(environment_contract&&) noexcept {
    return *this;
  }
};

template<structure::typed_port Source, structure::typed_port Destination>
struct face_contract final {
  using source_port_type = Source;
  using destination_port_type = Destination;
};

}  // namespace holonics::codec
