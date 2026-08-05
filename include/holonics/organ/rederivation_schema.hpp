#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/config.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t rederivation_external_count = 7;
inline constexpr std::size_t rederivation_coefficient_count = 49;
inline constexpr std::size_t rederivation_jacobian_count = 2'401;
inline constexpr std::size_t rederivation_injection_capacity = 800;
inline constexpr std::size_t rederivation_polygon_count = 4;
inline constexpr std::size_t rederivation_vertex_capacity = 6;
inline constexpr std::size_t rederivation_dilation_count = 5;
inline constexpr std::size_t rederivation_lattice_x_capacity = 21;
inline constexpr std::size_t rederivation_lattice_y_capacity = 13;
inline constexpr std::size_t rederivation_subset_count = 70;
inline constexpr std::size_t rederivation_word_count = 8;
inline constexpr std::size_t rederivation_word_width = 3;
inline constexpr std::size_t rederivation_pair_count = 64;

struct rederivation_point final {
  std::int16_t x{};
  std::int16_t y{};
};

struct rederivation_card_metadata final {
  exact::word schema{};
  exact::word occurrence{};
  std::uint32_t byte_count{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  exact::word lineage{};
  bool parsed{};
};

struct matching_problem_card final {
  rederivation_card_metadata metadata{};
  std::uint8_t matrix_size{};
  std::uint8_t marked_count{};
  std::uint8_t side_count{};
  std::uint8_t external_count{};
  std::int16_t p[rederivation_external_count]{};
  std::int16_t q[rederivation_external_count]{};
};

struct rederivation_polygon_source final {
  std::uint8_t vertex_count{};
  rederivation_point vertices[rederivation_vertex_capacity]{};
  exact::word identity{};
  exact::word lineage{};
};

struct lattice_problem_card final {
  rederivation_card_metadata metadata{};
  rederivation_polygon_source polygons[rederivation_polygon_count]{};
  std::uint8_t dilation_max{};
  std::uint8_t potential_polygon{};
  std::int16_t boundary_x_coefficient{};
  std::int16_t boundary_y_coefficient{};
};

struct cover_problem_card final {
  rederivation_card_metadata metadata{};
  std::uint8_t alphabet{};
  std::uint8_t words{};
  std::uint8_t maximum_width{};
  std::uint8_t subset_size{};
};

struct rederivation_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct rederivation_foundation final {
  matching_problem_card matching{};
  lattice_problem_card lattice{};
  cover_problem_card cover{};
  exact::word event{};
  exact::word incoming_port{};
  exact::word return_port{};
  exact::word lineage{};
};

} // namespace holonics::organ
