#pragma once

#include <cuda_runtime_api.h>

namespace holonics::apparatus {

struct elementary_current_set final { cudaStream_t currents[5]{}; };
struct heldout_current_set final { cudaStream_t source{}; cudaStream_t organ{}; };
[[nodiscard]] bool open_elementary_currents(elementary_current_set &) noexcept;
[[nodiscard]] bool join_elementary_currents(const elementary_current_set &) noexcept;
void close_elementary_currents(elementary_current_set &) noexcept;
[[nodiscard]] bool open_heldout_currents(heldout_current_set &) noexcept;
void close_heldout_currents(heldout_current_set &) noexcept;

}  // namespace holonics::apparatus
