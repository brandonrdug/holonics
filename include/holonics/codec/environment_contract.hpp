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

// `face_contract` stood here: two type aliases, no members, no callables, and no
// constraint beyond what `structure::typed_port` already imposes at every use
// site. It named the record's contact requirement -- a typed pullback yielding
// zero, one, or plural organs with an obstruction at zero-match and at
// unresolved plurality (`PURE_HOLONIC_ENGINE.md:100-107`) -- and typed none of
// it. Removed 2026-08-06; the requirement it named is owed, not deleted.

}  // namespace holonics::codec
