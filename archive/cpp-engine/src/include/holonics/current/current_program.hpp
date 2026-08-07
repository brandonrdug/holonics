#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/rest_record.hpp>
#include <holonics/exact/word.hpp>
#include <holonics/structure/port.hpp>

namespace holonics::current {

inline constexpr std::size_t program_site_capacity = 16;
inline constexpr std::size_t program_arc_capacity = 24;
inline constexpr std::size_t sparse_current_capacity = 16;
inline constexpr std::size_t program_front_capacity = 8;
inline constexpr std::size_t program_component_capacity = 4;
inline constexpr std::size_t current_case_capacity = 4;
inline constexpr std::size_t current_delta_capacity = 64;

struct current_input_payload final { exact::word value{}; };
struct current_output_payload final { exact::word value{}; };
using current_input_port =
    structure::port<current_input_payload, structure::port_direction::inbound>;
using current_output_port =
    structure::port<current_output_payload, structure::port_direction::outbound>;

struct morphology_cell final {
  exact::word scale{};
  exact::word offset{};
  exact::word passages{};
};

struct current_site final {
  exact::word identity{};
  exact::word support{};
  exact::word outbound_port{};
  std::uint16_t first_arc{};
  std::uint16_t arc_count{};
  std::uint8_t component{};
};

struct current_arc final {
  exact::word port{};
  exact::word lineage{};
  std::uint16_t target{};
  std::uint16_t multiplicity{};
};

struct sparse_current final {
  exact::word occurrence{};
  exact::word lineage{};
  exact::word local_state{};
  exact::word caused_support{};
  std::uint16_t site{};
  std::uint16_t phase{};
  std::uint16_t multiplicity{};
  std::uint8_t component{};
  bool open{};
};

struct causal_program final {
  exact::word identity{};
  exact::word predecessor{};
  exact::word input_port{};
  exact::word output_port{};
  exact::word lineage{};
  exact::word receiver_support{};
  exact::word next_occurrence{};
  exact::word next_event{};
  std::uint16_t site_count{};
  std::uint16_t arc_count{};
  std::uint16_t initial_current_count{};
  std::uint16_t resource_obligation{};
  std::uint8_t component_count{};
  std::uint8_t receiver_front_aperture{};
  body::rest_region body_regions[body::live_region_capacity]{};
  current_site sites[program_site_capacity]{};
  current_arc arcs[program_arc_capacity]{};
  morphology_cell morphology[program_site_capacity]{};
  sparse_current initial_currents[sparse_current_capacity]{};
};

struct current_mount_batch final {
  std::uint16_t count{};
  causal_program programs[current_case_capacity]{};
};

static_assert(structure::typed_port<current_input_port>);
static_assert(structure::typed_port<current_output_port>);

}  // namespace holonics::current
