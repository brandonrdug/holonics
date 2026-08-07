#pragma once

#include <holonics/current/weave_receipt.hpp>
#include <holonics/receiver/geometry_receipt.hpp>

namespace holonics::apparatus {

struct receiver_geometry_mount final {
  current::weave_program current{};
  receiver::geometry_program receiver{};
};

struct receiver_geometry_observation final {
  current::weave_snapshot current_predecessor{};
  current::weave_snapshot current_successor{};
  receiver::geometry_observation receiver{};
  bool current_returned{};
};

}  // namespace holonics::apparatus
