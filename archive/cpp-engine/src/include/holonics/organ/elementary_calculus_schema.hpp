#pragma once

#include <cstdint>

#include <holonics/organ/cultivated_organ_schema.hpp>

namespace holonics::organ {

inline constexpr std::uint8_t elementary_coordinate_count = 5;
inline constexpr std::uint8_t elementary_occurrence_count = 6;
inline constexpr std::uint8_t elementary_edge_count = 5;
inline constexpr std::uint8_t elementary_face_count = 2;
inline constexpr std::uint8_t elementary_composition_count = 5;
inline constexpr std::uint8_t elementary_source_count = 6;
inline constexpr std::uint8_t elementary_conduct_field_count = 7;
inline constexpr std::uint8_t elementary_conduct_case_count = 8;
inline constexpr std::uint16_t elementary_conduct_candidate_count = 2187;
inline constexpr std::uint8_t elementary_trace_count = 9;

struct exact_matrix2 final { std::int64_t value[4]{}; };

struct occurrence_incidence_card final {
  cultivation_card_metadata metadata{};
  std::uint64_t coordinates[elementary_occurrence_count][elementary_coordinate_count]{};
  std::int64_t payload[elementary_occurrence_count]{};
  std::int8_t boundary_one[4][elementary_edge_count]{};
  std::int8_t boundary_two[elementary_edge_count][elementary_face_count]{};
  std::uint8_t occurrence_count{};
};

struct composition_case_card final {
  std::int64_t forward[4]{};
  std::int64_t reverse[4]{};
  std::uint8_t visible{};
  bool contact{};
  bool predecessor_link{};
  bool forward_available{};
  bool reverse_available{};
};

struct composition_card final {
  cultivation_card_metadata metadata{};
  composition_case_card cases[elementary_composition_count]{};
  std::uint8_t case_count{};
};

struct receiver_card final {
  cultivation_card_metadata metadata{};
  std::int64_t coarse[elementary_source_count]{};
  std::int64_t fine[elementary_source_count]{};
  std::int64_t first_consequence[elementary_source_count]{};
  std::int64_t strict_consequence[elementary_source_count]{};
  std::uint8_t source_count{};
};

struct local_chart_card final {
  cultivation_card_metadata metadata{};
  exact_matrix2 first{};
  exact_matrix2 second{};
};

struct conduct_case_card final {
  std::uint8_t fields[elementary_conduct_field_count]{};
  bool changed_conduct{};
};

struct return_conduct_card final {
  cultivation_card_metadata metadata{};
  conduct_case_card cases[elementary_conduct_case_count]{};
  std::uint8_t case_count{};
};

struct elementary_development_bundle final {
  occurrence_incidence_card occurrence{};
  composition_card composition{};
  receiver_card receiver{};
  local_chart_card chart{};
  return_conduct_card conduct{};
};

struct heldout_triangle_card final {
  cultivation_card_metadata metadata{};
  exact_matrix2 edges[3]{};
  std::uint8_t maximum_horizon{};
  std::uint8_t changed_slot{};
  std::int64_t changed_value{};
};

}  // namespace holonics::organ
