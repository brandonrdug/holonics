#include <cuda_runtime.h>

#include <holonics/apparatus/cm_incidence_probe.hpp>
#include <holonics/apparatus/cm_incidence_resident.hpp>

namespace holonics::apparatus {

cm_probe_receipt probe_cm_derivation(const organ::cm_incidence_foundation& foundation,
    organ::cm_incidence_receipt& returned) noexcept {
  cm_probe_receipt receipt{};
  if (!organ::cm_incidence_detail::valid_foundation(foundation)) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = cm_probe_status::device_unavailable; return receipt;
  }
  cm_incidence_mount* mount = nullptr;
  event::cm_incidence_observation* observation = nullptr;
  if (cudaMalloc(&mount, sizeof(cm_incidence_mount)) != cudaSuccess ||
      cudaMalloc(&observation, sizeof(event::cm_incidence_observation)) != cudaSuccess) {
    if (mount != nullptr) { static_cast<void>(cudaFree(mount)); }
    if (observation != nullptr) { static_cast<void>(cudaFree(observation)); }
    receipt.state = cm_probe_status::allocation_refused; return receipt;
  }
  cm_incidence_mount host_mount{};
  host_mount.foundation = foundation;
  if (cudaMemset(observation, 0, sizeof(event::cm_incidence_observation)) != cudaSuccess ||
      cudaMemcpy(mount, &host_mount, sizeof(host_mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    static_cast<void>(cudaFree(mount));
    static_cast<void>(cudaFree(observation));
    receipt.state = cm_probe_status::transfer_refused; return receipt;
  }
  const bool launched = launch_cm_translations(mount, observation) == cudaSuccess &&
      launch_cm_periodic(observation) == cudaSuccess &&
      launch_cm_window(observation) == cudaSuccess &&
      launch_cm_characteristics(mount, observation) == cudaSuccess &&
      cudaDeviceSynchronize() == cudaSuccess &&
      cudaMemcpy(&returned, &observation->inquiry, sizeof(returned),
          cudaMemcpyDeviceToHost) == cudaSuccess;
  static_cast<void>(cudaFree(mount));
  static_cast<void>(cudaFree(observation));
  if (!launched) { receipt.state = cm_probe_status::derivation_refused; return receipt; }
  receipt.state = cm_probe_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(host_mount)};
  receipt.bytes_from_device = exact::word{sizeof(returned)};
  receipt.kernel_launches = exact::word{4};
  receipt.launched_threads = exact::word{5};
  return receipt;
}

}  // namespace holonics::apparatus
