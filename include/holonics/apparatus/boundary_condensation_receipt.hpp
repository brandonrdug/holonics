#pragma once

#include <holonics/body/rest_record.hpp>
#include <holonics/receiver/condensation_receipt.hpp>

namespace holonics::apparatus {

struct boundary_condensation_mount final {
  receiver::condensation_program program{};
  body::rest_region body_regions[body::live_region_capacity]{};
};

struct boundary_condensation_observation final {
  receiver::condensation_observation semantic{};
};

}  // namespace holonics::apparatus
