#include <cuda_runtime.h>

#include <holonics/apparatus/algebraic_variation_probe.hpp>
#include <holonics/apparatus/algebraic_variation_resident.hpp>

namespace holonics::apparatus {

variation_probe_receipt probe_algebraic_variation(
    const organ::algebraic_variation_foundation& foundation,
    organ::algebraic_variation_receipt& returned) noexcept {
  variation_probe_receipt receipt{};
  if (!organ::variation_polynomial_detail::valid_foundation(foundation)) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = variation_probe_status::device_unavailable; return receipt;
  }
  algebraic_variation_mount* mount = nullptr;
  event::algebraic_variation_observation* observation = nullptr;
  if (cudaMalloc(&mount, sizeof(algebraic_variation_mount)) != cudaSuccess ||
      cudaMalloc(&observation, sizeof(event::algebraic_variation_observation)) != cudaSuccess) {
    if (mount != nullptr) { static_cast<void>(cudaFree(mount)); }
    if (observation != nullptr) { static_cast<void>(cudaFree(observation)); }
    receipt.state = variation_probe_status::allocation_refused; return receipt;
  }
  algebraic_variation_mount host_mount{}; host_mount.foundation = foundation;
  host_mount.question = {exact::word{191'320}, exact::word{191'321}, exact::word{191'322}};
  if (cudaMemset(observation, 0, sizeof(event::algebraic_variation_observation)) != cudaSuccess ||
      cudaMemcpy(mount, &host_mount, sizeof(host_mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    static_cast<void>(cudaFree(mount)); static_cast<void>(cudaFree(observation));
    receipt.state = variation_probe_status::transfer_refused; return receipt;
  }
  const bool launched = launch_variation_derive(mount, observation) == cudaSuccess &&
      cudaDeviceSynchronize() == cudaSuccess &&
      cudaMemcpy(&returned, &observation->inquiry, sizeof(returned),
          cudaMemcpyDeviceToHost) == cudaSuccess;
  static_cast<void>(cudaFree(mount)); static_cast<void>(cudaFree(observation));
  if (!launched) { receipt.state = variation_probe_status::derivation_refused; return receipt; }
  receipt.state = variation_probe_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(host_mount)};
  receipt.bytes_from_device = exact::word{sizeof(returned)};
  receipt.kernel_launches = exact::word{1}; receipt.launched_threads = exact::word{1};
  return receipt;
}

}  // namespace holonics::apparatus
