#include <cuda_runtime.h>

#include <holonics/apparatus/toric_cycle_probe.hpp>
#include <holonics/apparatus/toric_cycle_resident.hpp>

namespace holonics::apparatus {

toric_probe_receipt probe_toric_derivation(
    const organ::toric_cycle_foundation& foundation,
    organ::toric_cycle_receipt& returned) noexcept {
  toric_probe_receipt receipt{};
  if (!organ::toric_fan_detail::valid_foundation(foundation)) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = toric_probe_status::device_unavailable; return receipt;
  }
  toric_cycle_mount* mount = nullptr;
  event::toric_cycle_observation* observation = nullptr;
  if (cudaMalloc(&mount, sizeof(toric_cycle_mount)) != cudaSuccess ||
      cudaMalloc(&observation, sizeof(event::toric_cycle_observation)) != cudaSuccess) {
    if (mount != nullptr) { static_cast<void>(cudaFree(mount)); }
    if (observation != nullptr) { static_cast<void>(cudaFree(observation)); }
    receipt.state = toric_probe_status::allocation_refused; return receipt;
  }
  toric_cycle_mount host_mount{}; host_mount.foundation = foundation;
  if (cudaMemset(observation, 0, sizeof(event::toric_cycle_observation)) != cudaSuccess ||
      cudaMemcpy(mount, &host_mount, sizeof(host_mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    static_cast<void>(cudaFree(mount)); static_cast<void>(cudaFree(observation));
    receipt.state = toric_probe_status::transfer_refused; return receipt;
  }
  const bool launched = launch_toric_derive(mount, observation) == cudaSuccess &&
      cudaDeviceSynchronize() == cudaSuccess &&
      cudaMemcpy(&returned, &observation->inquiry, sizeof(returned),
          cudaMemcpyDeviceToHost) == cudaSuccess;
  static_cast<void>(cudaFree(mount)); static_cast<void>(cudaFree(observation));
  if (!launched) { receipt.state = toric_probe_status::derivation_refused; return receipt; }
  receipt.state = toric_probe_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(host_mount)};
  receipt.bytes_from_device = exact::word{sizeof(returned)};
  receipt.kernel_launches = exact::word{1}; receipt.launched_threads = exact::word{1};
  return receipt;
}

}  // namespace holonics::apparatus
