#pragma once

#include <holonics/structure/identity.hpp>

namespace holonics::receiver {

struct chart_identity_owner final {};

struct chart_contract final {
  using identity_type = structure::identity<chart_identity_owner>;
};

}  // namespace holonics::receiver
