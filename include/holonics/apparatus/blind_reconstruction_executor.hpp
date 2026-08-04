#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/current/logical_resource_receipt.hpp>
#include <holonics/event/resident_blind_reconstruction_return.hpp>

namespace holonics::apparatus {

struct blind_reconstruction_mount final {
  organ::blind_reconstruction_foundation foundation{};
  organ::blind_reconstruction_question question{};
  event::regular_singular_rest_record inherited{};
};

enum class blind_reconstruction_executor_status : std::uint8_t {
  returned,
  invalid_mount,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  reconstruction_refused,
  code_formation_refused,
  code_process_refused,
  code_return_refused,
  moment_formation_refused,
  moment_process_refused,
  moment_return_refused,
  rest_refused
};

struct blind_checker_configuration final {
  lean_process_configuration code{};
  lean_process_configuration moment{};
};

struct blind_reconstruction_executor_receipt final {
  blind_reconstruction_executor_status state{
      blind_reconstruction_executor_status::invalid_mount};
  lean_process_receipt code_process{};
  lean_process_receipt moment_process{};
  current::logical_resource_receipt logical{};
  physical_telemetry_receipt physical{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word code_threads{};
  exact::word moment_threads{};
  exact::word host_semantic_events{};
  exact::word released_solution_reads{};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};

  [[nodiscard]] constexpr bool returned() const noexcept {
    return state == blind_reconstruction_executor_status::returned;
  }
};

[[nodiscard]] blind_reconstruction_executor_receipt execute_blind_reconstruction(
    const blind_reconstruction_mount& mount, const blind_checker_configuration& process,
    event::blind_reconstruction_observation& observation,
    event::blind_reconstruction_rest_record& handoff) noexcept;

}  // namespace holonics::apparatus
