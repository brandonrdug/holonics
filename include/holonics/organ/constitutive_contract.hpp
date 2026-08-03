#pragma once

#include <holonics/structure/port.hpp>

namespace holonics::organ {

template<structure::typed_port Input, structure::typed_port Output>
struct constitutive_contract final {
  using input_port_type = Input;
  using output_port_type = Output;
};

}  // namespace holonics::organ
