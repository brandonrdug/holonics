#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t blind_cube_dimension_capacity = 7;
inline constexpr std::size_t blind_cube_vertex_capacity = 128;
inline constexpr std::size_t blind_parity_row_capacity = 3;
inline constexpr std::size_t blind_codeword_capacity = 16;
inline constexpr std::size_t blind_pair_capacity = 3;
inline constexpr std::size_t blind_pair_cell_capacity = 20;
inline constexpr std::size_t blind_distance_capacity = 8;
inline constexpr std::size_t blind_moment_case_capacity = 5;
inline constexpr std::size_t blind_moment_capacity = 8;
inline constexpr std::size_t blind_moment_degree_capacity = 4;
inline constexpr std::size_t blind_polynomial_capacity = 5;
inline constexpr std::size_t blind_candidate_capacity = 4;

enum class blind_candidate_kind : std::uint8_t {
  shell_collapse,
  unit_grid,
  lineage_transpose,
  incidence_product,
  hankel,
  toeplitz,
  reversed_hankel,
  collapsed_degree
};

enum class blind_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  card_refused,
  code_incidence_refused,
  pair_factor_refused,
  moment_access_refused,
  singular_root_fiber,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct binary_code_problem_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  std::uint8_t dimension{};
  std::uint8_t row_count{};
  std::uint8_t parity_rows[blind_parity_row_capacity]{};
  bool parsed{};
};

struct moment_problem_case final {
  exact::word occurrence{};
  std::int64_t moments[blind_moment_capacity]{};
  std::int16_t aperture_min{};
  std::int16_t aperture_max{};
  std::uint8_t degree{};
  std::uint8_t moment_count{};
};

struct moment_problem_card final {
  exact::word schema{};
  exact::word lineage{};
  moment_problem_case cases[blind_moment_case_capacity]{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  std::uint8_t case_count{};
  bool parsed{};
};

struct blind_reconstruction_foundation final {
  exact::word ecology{};
  exact::word code_incidence{};
  exact::word orthogonal_transport{};
  exact::word moment_transport{};
  exact::word characteristic_transport{};
  exact::word candidate_transport{};
  exact::word provenance{};
  binary_code_problem_card code{};
  moment_problem_card moments{};
};

struct blind_reconstruction_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct blind_theory_plan final {
  exact::word code_passage{};
  exact::word moment_passage{};
  exact::word code_statement{};
  exact::word moment_statement{};
  exact::word lineage{};
  bool code_incidence{};
  bool jacobi_transport{};
  bool moment_pencil{};
  bool separability_boundary{};
  bool alternatives_retained{};
  bool source_separated{};
};

struct acquired_blind_reconstruction final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
