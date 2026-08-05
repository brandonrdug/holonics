#include <holonics/apparatus/trace_rebase_current_set.hpp>

namespace holonics::apparatus {

bool open_trace_rebase_currents(trace_rebase_current_set &out) noexcept {
  for (auto &current : out.currents)
    if (cudaStreamCreateWithFlags(&current, cudaStreamNonBlocking) != cudaSuccess) {
      close_trace_rebase_currents(out);
      return false;
    }
  return true;
}
bool join_trace_rebase_currents(const trace_rebase_current_set &currents) noexcept {
  bool exact = true;
  for (const auto current : currents.currents)
    exact = exact && cudaStreamSynchronize(current) == cudaSuccess;
  return exact;
}
void close_trace_rebase_currents(trace_rebase_current_set &out) noexcept {
  for (auto &current : out.currents) {
    if (current != nullptr)
      static_cast<void>(cudaStreamDestroy(current));
    current = nullptr;
  }
}
bool open_trace_rebase_heldout_currents(
    trace_rebase_heldout_currents &out) noexcept {
  if (cudaStreamCreateWithFlags(&out.source, cudaStreamNonBlocking) !=
      cudaSuccess)
    return false;
  if (cudaStreamCreateWithFlags(&out.organ, cudaStreamNonBlocking) !=
      cudaSuccess) {
    close_trace_rebase_heldout_currents(out);
    return false;
  }
  return true;
}
void close_trace_rebase_heldout_currents(
    trace_rebase_heldout_currents &out) noexcept {
  if (out.source != nullptr)
    static_cast<void>(cudaStreamDestroy(out.source));
  if (out.organ != nullptr)
    static_cast<void>(cudaStreamDestroy(out.organ));
  out = {};
}

} // namespace holonics::apparatus
