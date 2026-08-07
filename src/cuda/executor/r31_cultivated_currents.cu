#include <holonics/apparatus/cultivated_current_set.hpp>

namespace holonics::apparatus {

void close_cultivated_currents(cultivated_current_set &set) noexcept {
  for (auto &stream : set.currents) if (stream) cudaStreamDestroy(stream);
  set = {};
}
bool open_cultivated_currents(cultivated_current_set &set) noexcept {
  for (auto &stream : set.currents)
    if (cudaStreamCreateWithFlags(&stream, cudaStreamNonBlocking) != cudaSuccess) {
      close_cultivated_currents(set); return false;
    }
  return true;
}
bool join_cultivated_currents(const cultivated_current_set &set) noexcept {
  for (const auto stream : set.currents)
    if (cudaStreamSynchronize(stream) != cudaSuccess) return false;
  return true;
}

}  // namespace holonics::apparatus
