#pragma once

#include <cuda_runtime_api.h>

namespace holonics::apparatus {

struct trace_fiber_current_set final { cudaStream_t currents[3]{}; };
struct trace_fiber_heldout_currents final {
  cudaStream_t source{};
  cudaStream_t organ{};
};
[[nodiscard]] bool open_trace_fiber_currents(trace_fiber_current_set &) noexcept;
[[nodiscard]] bool join_trace_fiber_currents(
    const trace_fiber_current_set &) noexcept;
void close_trace_fiber_currents(trace_fiber_current_set &) noexcept;
[[nodiscard]] bool open_trace_fiber_heldout_currents(
    trace_fiber_heldout_currents &) noexcept;
void close_trace_fiber_heldout_currents(trace_fiber_heldout_currents &) noexcept;

} // namespace holonics::apparatus
