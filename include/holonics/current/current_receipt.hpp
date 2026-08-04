#pragma once

#include <cstdint>

#include <holonics/current/current_program.hpp>

namespace holonics::current {

enum class current_status : std::uint8_t {
  unmounted,
  mounted,
  exact_rest,
  open_frontier,
  obstructed
};

enum class current_obstruction : std::uint8_t {
  none,
  invalid_program,
  capacity_refused,
  arithmetic_overflow,
  reservation_conflict,
  receiver_aperture,
  device_unavailable
};

struct local_pending_deed final {
  exact::word predecessor{};
  exact::word event{};
  exact::word current_occurrence{};
  exact::word caused_support{};
  exact::word lineage{};
  std::uint16_t source_site{};
  bool active{};
};

struct current_delta final {
  exact::word predecessor{};
  exact::word input_event{};
  exact::word return_event{};
  exact::word read_support{};
  exact::word change_support{};
  std::int64_t incidence_delta{};
  exact::word morphology_delta{};
  exact::word successor_current{};
  exact::word returned_consequence{};
  exact::word stress{};
  exact::word obstruction{};
  exact::word logical_resource{};
  exact::word lineage{};
  std::uint16_t source_site{};
  std::uint16_t successor_count{};
};

struct front_receipt final {
  exact::word predecessor{};
  exact::word successor{};
  exact::word event_first{};
  exact::word read_support{};
  exact::word change_support{};
  exact::word current_fold{};
  std::uint16_t input_count{};
  std::uint16_t output_count{};
  std::uint16_t reservations{};
  std::uint16_t pending_before{};
  std::uint16_t pending_after{};
};

struct component_quiescence final {
  std::uint16_t local_current{};
  std::uint16_t in_flight{};
  bool certified{};
};

struct current_observation final {
  exact::word program_identity{};
  exact::word predecessor{};
  exact::word successor{};
  exact::word receiver_support{};
  exact::word touched_support{};
  current_status state{current_status::unmounted};
  current_obstruction obstruction{current_obstruction::none};
  std::uint16_t front_count{};
  std::uint16_t final_current_count{};
  std::uint16_t local_pending_count{};
  std::uint16_t delta_count{};
  bool compositional_quiescence{};
  bool source_detached{};
  front_receipt fronts[program_front_capacity]{};
  component_quiescence components[program_component_capacity]{};
  sparse_current final_currents[sparse_current_capacity]{};
  morphology_cell morphology[program_site_capacity]{};
  current_delta deltas[current_delta_capacity]{};
};

struct current_batch_observation final {
  std::uint16_t count{};
  current_observation cases[current_case_capacity]{};
};

}  // namespace holonics::current
