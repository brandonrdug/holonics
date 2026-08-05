#pragma once

#include <cuda_runtime_api.h>

namespace holonics::apparatus {

struct rederivation_current_set final {
  cudaStream_t matching{};
  cudaStream_t geometry{};
  cudaStream_t cover{};
};

[[nodiscard]] bool
open_rederivation_currents(rederivation_current_set &) noexcept;
[[nodiscard]] bool
join_rederivation_currents(const rederivation_current_set &) noexcept;
void close_rederivation_currents(rederivation_current_set &) noexcept;

} // namespace holonics::apparatus
