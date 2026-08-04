#include <cuda_runtime.h>

#include <holonics/apparatus/blind_reconstruction_probe.hpp>
#include <holonics/apparatus/blind_reconstruction_resident.hpp>

namespace holonics::apparatus {

blind_probe_receipt probe_blind_derivation(
    const organ::blind_reconstruction_foundation& foundation,
    organ::blind_reconstruction_receipt& returned) noexcept {
  blind_probe_receipt receipt{};
  if (!organ::blind_reconstruction_detail::valid_foundation(foundation)) { return receipt; }
  int device_count = 0;
  if (cudaGetDeviceCount(&device_count) != cudaSuccess || device_count <= 0 ||
      cudaSetDevice(0) != cudaSuccess) {
    receipt.state = blind_probe_status::device_unavailable;
    return receipt;
  }
  blind_reconstruction_mount* mount = nullptr;
  event::blind_reconstruction_observation* observation = nullptr;
  if (cudaMalloc(&mount, sizeof(blind_reconstruction_mount)) != cudaSuccess ||
      cudaMalloc(&observation, sizeof(event::blind_reconstruction_observation)) != cudaSuccess) {
    if (mount != nullptr) { static_cast<void>(cudaFree(mount)); }
    if (observation != nullptr) { static_cast<void>(cudaFree(observation)); }
    receipt.state = blind_probe_status::allocation_refused;
    return receipt;
  }
  blind_reconstruction_mount host_mount{};
  host_mount.foundation = foundation;
  if (cudaMemset(observation, 0, sizeof(event::blind_reconstruction_observation)) != cudaSuccess ||
      cudaMemcpy(mount, &host_mount, sizeof(host_mount), cudaMemcpyHostToDevice) != cudaSuccess) {
    static_cast<void>(cudaFree(mount));
    static_cast<void>(cudaFree(observation));
    receipt.state = blind_probe_status::transfer_refused;
    return receipt;
  }
  const bool launched = launch_blind_code(mount, observation) == cudaSuccess &&
      launch_blind_pairs(mount, observation) == cudaSuccess &&
      launch_blind_moments(mount, observation) == cudaSuccess &&
      cudaDeviceSynchronize() == cudaSuccess &&
      cudaMemcpy(&returned, &observation->inquiry, sizeof(returned),
          cudaMemcpyDeviceToHost) == cudaSuccess;
  static_cast<void>(cudaFree(mount));
  static_cast<void>(cudaFree(observation));
  if (!launched) {
    receipt.state = blind_probe_status::derivation_refused;
    return receipt;
  }
  receipt.state = blind_probe_status::returned;
  receipt.bytes_to_device = exact::word{sizeof(host_mount)};
  receipt.bytes_from_device = exact::word{sizeof(returned)};
  receipt.kernel_launches = exact::word{3};
  receipt.launched_threads = exact::word{9};
  return receipt;
}

}  // namespace holonics::apparatus
