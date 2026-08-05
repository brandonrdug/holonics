#include <holonics/apparatus/rederivation_current_set.hpp>

namespace holonics::apparatus {

void close_rederivation_currents(rederivation_current_set &set) noexcept {
  if (set.cover)
    cudaStreamDestroy(set.cover);
  if (set.geometry)
    cudaStreamDestroy(set.geometry);
  if (set.matching)
    cudaStreamDestroy(set.matching);
  set = {};
}

bool open_rederivation_currents(rederivation_current_set &set) noexcept {
  if (cudaStreamCreateWithFlags(&set.matching, cudaStreamNonBlocking) !=
          cudaSuccess ||
      cudaStreamCreateWithFlags(&set.geometry, cudaStreamNonBlocking) !=
          cudaSuccess ||
      cudaStreamCreateWithFlags(&set.cover, cudaStreamNonBlocking) !=
          cudaSuccess) {
    close_rederivation_currents(set);
    return false;
  }
  return true;
}

bool join_rederivation_currents(const rederivation_current_set &set) noexcept {
  return cudaStreamSynchronize(set.matching) == cudaSuccess &&
         cudaStreamSynchronize(set.geometry) == cudaSuccess &&
         cudaStreamSynchronize(set.cover) == cudaSuccess;
}

} // namespace holonics::apparatus
