#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/rest_record.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::current {

inline constexpr std::size_t weave_cell_capacity = 12;
inline constexpr std::size_t weave_event_capacity = 10;
inline constexpr std::size_t weave_variant_capacity = 4;
inline constexpr std::size_t coherence_permutation_capacity = 6;
inline constexpr std::size_t weave_case_capacity = 2;
inline constexpr std::size_t weave_layer_capacity = 6;

enum class weave_obstruction : std::uint8_t {
  none,
  invalid_program,
  unproved_overlap,
  logical_resource_refused,
  returned_resource_open,
  invalid_interaction
};

struct weave_cell final {
  exact::word identity{};
  exact::word value{};
  exact::word morphology{};
  exact::word current{};
  exact::word lineage{};
  std::uint16_t placement{};
  std::uint16_t aperture{};
};

struct logical_resource_state final {
  exact::word capacity{};
  exact::word used{};
  exact::word reservations[weave_event_capacity]{};
};

struct weave_snapshot final {
  exact::word head{};
  exact::word incidence{};
  exact::word lineage_order{};
  exact::word emitted[weave_event_capacity]{};
  weave_cell cells[weave_cell_capacity]{};
  logical_resource_state logical{};
  weave_obstruction obstruction{weave_obstruction::none};
  std::uint16_t cell_count{};
  std::uint16_t event_count{};
};

struct weave_event final {
  exact::word identity{};
  exact::word input_port{};
  exact::word output_port{};
  exact::word lineage{};
  exact::word read_support{};
  exact::word change_support{};
  exact::word value_delta{};
  exact::word morphology_delta{};
  exact::word successor_current{};
  exact::word consequence{};
  exact::word stress{};
  exact::word logical_resource{};
  exact::word interaction{};
  std::uint16_t cell{};
};

struct weave_delta final {
  exact::word predecessor{};
  exact::word event{};
  exact::word input_port{};
  exact::word output_port{};
  exact::word read_support{};
  exact::word change_support{};
  exact::word value_delta{};
  exact::word morphology_delta{};
  exact::word successor_current{};
  exact::word consequence{};
  exact::word stress{};
  exact::word obstruction{};
  exact::word logical_resource{};
  exact::word lineage{};
  exact::word interaction{};
  std::uint16_t cell{};
};

struct resource_return final {
  exact::word occurrence{};
  exact::word port{};
  exact::word lineage{};
  exact::word available_bytes{};
  exact::word resident_bytes{};
  exact::word temperature_upper_millikelvin{};
};

struct resource_policy final {
  exact::word expected_port{};
  exact::word required_bytes{};
  exact::word temperature_limit_millikelvin{};
  std::uint16_t alternative_partition{};
  std::uint16_t alternative_aperture{};
  bool alternative_declared{};
};

struct weave_program final {
  exact::word identity{};
  exact::word predecessor{};
  exact::word incidence{};
  exact::word lineage_seed{};
  exact::word logical_capacity{};
  exact::word unproved_left_support{};
  exact::word unproved_right_support{};
  weave_cell cells[weave_cell_capacity]{};
  weave_event events[weave_event_capacity]{};
  resource_policy resource{};
  resource_return returned_resource{};
  body::rest_region body_regions[body::live_region_capacity]{};
  std::uint16_t cell_count{};
  std::uint16_t event_count{};
  std::uint16_t interaction_left{};
  std::uint16_t interaction_right{};
  std::uint16_t recurrence_first{};
  std::uint16_t recurrence_second{};
  std::uint16_t layer_offsets[weave_layer_capacity]{};
  std::uint16_t layer_counts[weave_layer_capacity]{};
  std::uint16_t variant_orders[weave_variant_capacity][weave_event_capacity]{};
  std::uint16_t variant_partitions[weave_variant_capacity]{};
  std::uint16_t layer_count{};
};

struct weave_mount_batch final {
  std::uint16_t count{};
  weave_program programs[weave_case_capacity]{};
};

}  // namespace holonics::current
