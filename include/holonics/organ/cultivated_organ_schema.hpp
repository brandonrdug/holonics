#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/small_rational.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::uint8_t cultivation_family_count = 4;
inline constexpr std::uint8_t cultivation_series_capacity = 4;
inline constexpr std::uint8_t cultivation_sample_capacity = 10;
inline constexpr std::uint8_t cultivation_candidate_count = 9;
inline constexpr std::uint8_t cultivation_feature_capacity = 12;
inline constexpr std::uint8_t cultivation_row_capacity = 28;

enum class cultivation_family : std::uint8_t {
  reciprocal,
  central_walk,
  signed_trace,
  polygon_incidence
};

struct cultivation_card_metadata final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word incoming_port{};
  exact::word return_port{};
  exact::word lineage{};
  bool parsed{};
};

struct developmental_stream_card final {
  cultivation_card_metadata metadata{};
  exact::small_rational samples[cultivation_series_capacity]
                               [cultivation_sample_capacity]{};
  std::uint8_t sample_count[cultivation_series_capacity]{};
  std::uint8_t series_count{};
  std::uint8_t maximum_order{};
  std::uint8_t maximum_degree{};
  cultivation_family family{};
};

struct star_structure_card final {
  cultivation_card_metadata metadata{};
  std::uint8_t first_branch_count{};
  std::uint8_t last_branch_count{};
  std::int16_t common_conductance{};
  std::int16_t changed_conductance{};
};

struct walk_structure_card final {
  cultivation_card_metadata metadata{};
  std::int8_t steps[4][2]{};
  std::uint8_t step_count{};
  std::uint8_t maximum_half_horizon{};
};

struct signed_carrier_card final {
  cultivation_card_metadata metadata{};
  std::int16_t matrix[4]{};
  std::uint8_t maximum_horizon{};
  std::uint8_t changed_slot{};
  std::int16_t changed_value{};
};

struct graded_structure_card final {
  cultivation_card_metadata metadata{};
  std::uint8_t generators{};
  std::uint8_t maximum_horizon{};
  std::uint8_t changed_generators{};
};

struct heldout_structure_bundle final {
  star_structure_card star{};
  walk_structure_card walk{};
  signed_carrier_card carrier{};
  graded_structure_card graded{};
};

}  // namespace holonics::organ
