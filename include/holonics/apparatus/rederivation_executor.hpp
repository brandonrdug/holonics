#pragma once

#include <cstdint>

#include <holonics/apparatus/lean_checker_process.hpp>
#include <holonics/apparatus/physical_telemetry_receipt.hpp>
#include <holonics/apparatus/rederivation_resident.hpp>

namespace holonics::apparatus {

enum class rederivation_executor_status : std::uint8_t {
  returned,
  invalid_mount,
  device_unavailable,
  allocation_refused,
  transfer_refused,
  derivation_refused,
  foil_formation_refused,
  foil_process_refused,
  foil_return_refused,
  valid_formation_refused,
  valid_process_refused,
  valid_return_refused,
  rest_refused
};
struct rederivation_process_configuration final {
  lean_process_configuration foil{};
  lean_process_configuration valid{};
};
struct rederivation_logical_receipt final {
  exact::word jacobian_entries{};
  exact::word lattice_slots{};
  exact::word subset_receipts{};
  exact::word pair_receipts{};
  exact::word theorem_families{};
};
struct rederivation_executor_receipt final {
  rederivation_executor_status state{
      rederivation_executor_status::invalid_mount};
  std::uint32_t device_major{};
  std::uint32_t device_minor{};
  exact::word bytes_to_device{};
  exact::word bytes_from_device{};
  exact::word resident_bytes{};
  exact::word kernel_launches{};
  exact::word launched_threads{};
  exact::word semantic_threads{};
  exact::word host_semantic_events{};
  exact::word source_currents{};
  exact::word dependency_barriers{};
  rederivation_logical_receipt logical{};
  lean_process_receipt foil_process{};
  lean_process_receipt valid_process{};
  physical_telemetry_receipt physical{};
  [[nodiscard]] bool returned() const noexcept {
    return state == rederivation_executor_status::returned;
  }
};

[[nodiscard]] rederivation_executor_receipt
execute_rederivation(const rederivation_mount &mount,
                     const rederivation_process_configuration &process,
                     event::rederivation_observation &observation,
                     organ::rederivation_workspace &workspace,
                     event::rederivation_rest_record &handoff) noexcept;

} // namespace holonics::apparatus
