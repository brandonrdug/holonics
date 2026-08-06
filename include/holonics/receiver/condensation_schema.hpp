#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::receiver {

inline constexpr std::size_t condensation_source_capacity = 8;
inline constexpr std::size_t condensation_query_capacity = 3;
inline constexpr std::size_t condensation_history_capacity = 4;
inline constexpr std::size_t condensation_group_capacity = 5;

struct future_receiver_family final {
  exact::word identity{};
  exact::word version{};
  exact::word admitted_input_support{};
  exact::word query_weights[condensation_query_capacity][condensation_source_capacity]{};
  std::uint16_t query_count{};
};

struct condensation_input final {
  exact::word occurrence{};
  exact::word port{};
  exact::word lineage{};
  exact::word delta{};
  exact::word required_family_version{};
  std::uint16_t source_cell{};
  std::uint16_t query{};
};

struct condensation_program final {
  exact::word identity{};
  exact::word predecessor{};
  exact::word incidence{};
  exact::word lineage{};
  exact::word admitted_tally{};
  exact::word current{};
  exact::word logical_resource{};
  exact::word alternatives{};
  exact::word reconstruction_capability{};
  exact::word refinement_occurrence{};
  exact::word refinement_lineage{};
  exact::word source_identities[condensation_source_capacity]{};
  exact::word source_values[condensation_source_capacity]{};
  std::uint16_t initial_groups[condensation_source_capacity]{};
  std::uint16_t refined_groups[condensation_source_capacity]{};
  future_receiver_family initial_family{};
  future_receiver_family refined_family{};
  condensation_input history[condensation_history_capacity]{};
  std::uint16_t source_count{};
  std::uint16_t initial_group_count{};
  std::uint16_t refined_group_count{};
  std::uint16_t refinement_after_history{};
};

}  // namespace holonics::receiver
