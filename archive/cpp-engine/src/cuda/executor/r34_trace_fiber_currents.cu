#include <holonics/apparatus/trace_fiber_current_set.hpp>

namespace holonics::apparatus {
bool open_trace_fiber_currents(trace_fiber_current_set &set) noexcept {
  for (auto &stream : set.currents)
    if (cudaStreamCreateWithFlags(&stream, cudaStreamNonBlocking) != cudaSuccess) {
      close_trace_fiber_currents(set);
      return false;
    }
  return true;
}
bool join_trace_fiber_currents(const trace_fiber_current_set &set) noexcept {
  for (const auto stream : set.currents)
    if (cudaStreamSynchronize(stream) != cudaSuccess)
      return false;
  return true;
}
void close_trace_fiber_currents(trace_fiber_current_set &set) noexcept {
  for (auto &stream : set.currents) {
    if (stream != nullptr)
      static_cast<void>(cudaStreamDestroy(stream));
    stream = nullptr;
  }
}
bool open_trace_fiber_heldout_currents(
    trace_fiber_heldout_currents &set) noexcept {
  if (cudaStreamCreateWithFlags(&set.source, cudaStreamNonBlocking) != cudaSuccess)
    return false;
  if (cudaStreamCreateWithFlags(&set.organ, cudaStreamNonBlocking) != cudaSuccess) {
    close_trace_fiber_heldout_currents(set);
    return false;
  }
  return true;
}
void close_trace_fiber_heldout_currents(
    trace_fiber_heldout_currents &set) noexcept {
  if (set.source != nullptr)
    static_cast<void>(cudaStreamDestroy(set.source));
  if (set.organ != nullptr)
    static_cast<void>(cudaStreamDestroy(set.organ));
  set = {};
}
} // namespace holonics::apparatus
