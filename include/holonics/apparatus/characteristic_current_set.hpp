#pragma once

#include <cuda_runtime_api.h>

namespace holonics::apparatus {

struct characteristic_current_set final {
  cudaStream_t currents[3]{};
};
struct characteristic_heldout_currents final {
  cudaStream_t source{};
  cudaStream_t organ{};
};
[[nodiscard]] bool
open_characteristic_currents(characteristic_current_set &) noexcept;
[[nodiscard]] bool
join_characteristic_currents(const characteristic_current_set &) noexcept;
void close_characteristic_currents(characteristic_current_set &) noexcept;
[[nodiscard]] bool open_characteristic_heldout_currents(
    characteristic_heldout_currents &) noexcept;
void close_characteristic_heldout_currents(
    characteristic_heldout_currents &) noexcept;

} // namespace holonics::apparatus
