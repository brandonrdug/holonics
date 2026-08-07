#pragma once

#include <holonics/exact/config.hpp>

namespace holonics::apparatus {

class resident_world_contract final {
 public:
  resident_world_contract() = delete;
  resident_world_contract(const resident_world_contract&) = delete;
  resident_world_contract& operator=(const resident_world_contract&) = delete;
  HOLONICS_CALLABLE resident_world_contract(resident_world_contract&&) noexcept {}
  HOLONICS_CALLABLE resident_world_contract& operator=(resident_world_contract&&) noexcept {
    return *this;
  }
};

}  // namespace holonics::apparatus
