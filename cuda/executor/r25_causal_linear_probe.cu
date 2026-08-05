#include <cuda_runtime.h>

#include <holonics/apparatus/causal_linear_probe.hpp>
#include <holonics/apparatus/causal_linear_resident.hpp>

namespace holonics::apparatus {

causal_linear_probe_receipt probe_causal_linear(
    const organ::causal_linear_foundation& foundation,
    organ::causal_linear_receipt& returned) noexcept {
  causal_linear_probe_receipt receipt{};
  if (!organ::causal_linear_detail::valid_foundation(foundation)) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = causal_linear_probe_status::device_unavailable; return receipt;
  }
  causal_linear_mount* mount = nullptr;
  event::causal_linear_observation* observation = nullptr;
  if (cudaMalloc(&mount, sizeof(causal_linear_mount)) != cudaSuccess ||
      cudaMalloc(&observation, sizeof(event::causal_linear_observation)) != cudaSuccess) {
    if (mount != nullptr) { static_cast<void>(cudaFree(mount)); }
    if (observation != nullptr) { static_cast<void>(cudaFree(observation)); }
    receipt.state = causal_linear_probe_status::allocation_refused; return receipt;
  }
  causal_linear_mount host_mount{}; host_mount.foundation = foundation;
  host_mount.question = {exact::word{192'320}, exact::word{192'321}, exact::word{192'322}};
  if (cudaMemset(observation, 0, sizeof(event::causal_linear_observation)) != cudaSuccess ||
      cudaMemcpy(mount, &host_mount, sizeof(host_mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    static_cast<void>(cudaFree(mount)); static_cast<void>(cudaFree(observation));
    receipt.state = causal_linear_probe_status::transfer_refused; return receipt;
  }
  const bool launched = launch_causal_linear_sources(mount, observation) == cudaSuccess &&
      cudaDeviceSynchronize() == cudaSuccess &&
      launch_causal_linear_controls(mount, observation) == cudaSuccess &&
      cudaDeviceSynchronize() == cudaSuccess &&
      launch_causal_linear_aggregate(mount, observation) == cudaSuccess &&
      cudaDeviceSynchronize() == cudaSuccess &&
      cudaMemcpy(&returned, &observation->inquiry, sizeof(returned),
          cudaMemcpyDeviceToHost) == cudaSuccess;
  static_cast<void>(cudaFree(mount)); static_cast<void>(cudaFree(observation));
  if (!launched) { receipt.state = causal_linear_probe_status::derivation_refused;
    return receipt; }
  receipt.state = causal_linear_probe_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(host_mount)};
  receipt.bytes_from_device = exact::word{sizeof(returned)};
  receipt.kernel_launches = exact::word{9}; receipt.launched_threads = exact::word{9};
  return receipt;
}

}  // namespace holonics::apparatus
