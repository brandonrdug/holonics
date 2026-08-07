#pragma once

#include <holonics/organ/blind_reconstruction_schema.hpp>

namespace holonics::organ {

struct blind_candidate_receipt final {
  blind_candidate_kind kind{};
  exact::word identity{};
  std::uint64_t lineage{};
  bool access_complete{};
  bool recurrence_exact{};
  bool contact_exact{};
  bool source_order_exact{};
  bool separable{};
  bool admitted{};
};

struct code_population_receipt final {
  exact::word identity{};
  std::uint8_t codewords[blind_codeword_capacity]{};
  std::int64_t krawtchouk[blind_distance_capacity][blind_distance_capacity]{};
  std::int64_t dual_numerators[blind_distance_capacity]{};
  std::int64_t dual_distribution[blind_distance_capacity]{};
  std::uint16_t distance_distribution[blind_distance_capacity]{};
  std::uint64_t lineage{};
  std::uint16_t vertex_count{};
  std::uint8_t codeword_count{};
  std::uint8_t minimum_distance{};
  bool parity_enumerated{};
  bool dual_moments_nonnegative{};
  bool exact{};
};

struct pair_incidence_receipt final {
  exact::word identity{};
  std::int16_t quotient[blind_pair_cell_capacity][blind_pair_cell_capacity]{};
  std::int64_t left_krawtchouk[blind_distance_capacity][blind_distance_capacity]{};
  std::int64_t right_krawtchouk[blind_distance_capacity][blind_distance_capacity]{};
  std::int64_t witness_vector[blind_pair_cell_capacity]{};
  std::uint16_t population[blind_pair_cell_capacity]{};
  std::int16_t characteristic_roots[blind_distance_capacity]{};
  std::uint8_t characteristic_multiplicity[blind_distance_capacity]{};
  blind_candidate_receipt candidates[blind_candidate_capacity]{};
  std::uint64_t lineage{};
  std::uint8_t source_word{};
  std::uint8_t target_word{};
  std::uint8_t distance{};
  std::uint8_t left_size{};
  std::uint8_t right_size{};
  std::uint8_t cell_count{};
  std::int16_t witness_eigenvalue{};
  bool equitable{};
  bool detailed_balance{};
  bool directions_commute{};
  bool characteristic_exact{};
  bool exact{};
};

struct moment_root_receipt final {
  exact::word identity{};
  std::int64_t hankel[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  std::int64_t shifted[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  std::int64_t pencil[blind_polynomial_capacity]{};
  std::int64_t newton[blind_polynomial_capacity]{};
  std::int64_t roots[blind_moment_degree_capacity]{};
  blind_candidate_receipt candidates[blind_candidate_capacity]{};
  std::uint64_t lineage{};
  std::int64_t hankel_determinant{};
  std::int64_t discriminant{};
  std::uint8_t degree{};
  std::uint8_t root_count{};
  bool access_complete{};
  bool pencil_newton_agree{};
  bool roots_remove_exactly{};
  bool vandermonde_square{};
  bool separable{};
  bool exact{};
  blind_obstruction obstruction{blind_obstruction::card_refused};
};

struct blind_reconstruction_receipt final {
  blind_reconstruction_question question{};
  binary_code_problem_card mounted_code{};
  moment_problem_card mounted_moments{};
  code_population_receipt code{};
  pair_incidence_receipt pairs[blind_pair_capacity]{};
  moment_root_receipt moments[blind_moment_case_capacity]{};
  blind_theory_plan theory{};
  blind_obstruction obstruction{blind_obstruction::invalid_foundation};
  std::uint8_t returned_pairs{};
  std::uint8_t returned_moments{};
  std::uint8_t separable_moments{};
  std::uint8_t obstructed_moments{};
  bool no_released_solution_access{};
  bool no_expected_operator{};
  bool no_expected_roots{};
  bool alternatives_retained{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
