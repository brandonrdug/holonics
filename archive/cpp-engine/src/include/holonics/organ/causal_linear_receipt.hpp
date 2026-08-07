#pragma once

#include <holonics/exact/small_rational.hpp>
#include <holonics/organ/causal_linear_schema.hpp>

namespace holonics::organ {

struct causal_integer_matrix final {
  std::int64_t values[causal_matrix_rows][causal_matrix_columns]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t rows{};
  std::uint8_t columns{};
  bool exact{};
};

struct causal_matrix_analysis final {
  exact::small_rational kernel[causal_kernel_capacity][causal_matrix_columns]{};
  std::uint8_t pivot_columns[causal_matrix_rows]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t rank{};
  std::uint8_t nullity{};
  std::uint8_t kernel_count{};
  bool exact{};
};

struct causal_characteristic_receipt final {
  std::int64_t coefficients[causal_polynomial_capacity]{};
  std::int64_t traces[causal_square_degree]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t degree{};
  std::uint8_t fixed_dimension{};
  bool exact{};
};

struct causal_phase_section final {
  causal_integer_matrix boundary_one{};
  causal_integer_matrix boundary_two{};
  causal_matrix_analysis boundary_one_analysis{};
  causal_matrix_analysis boundary_two_analysis{};
  causal_integer_matrix diagonal{};
  causal_characteristic_receipt diagonal_characteristic{};
  std::uint64_t vertex_lineage[causal_matrix_rows]{};
  std::uint64_t edge_lineage[causal_matrix_columns]{};
  std::uint64_t face_lineage[causal_matrix_rows]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t betti[3]{};
  std::uint8_t vertices{};
  std::uint8_t edges{};
  std::uint8_t faces{};
  std::uint8_t tours{};
  std::uint8_t tour_length{};
  bool boundary_composite_zero{};
  bool exact{};
};

struct causal_cm_section final {
  causal_integer_matrix incidence{};
  causal_matrix_analysis incidence_analysis{};
  causal_integer_matrix adjacency{};
  causal_characteristic_receipt adjacency_characteristic{};
  std::uint64_t edge_lineage[40]{};
  std::int64_t factor_roots[6]{};
  std::uint8_t factor_multiplicities[6]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t vertices{};
  std::uint8_t edges{};
  std::uint8_t homology_zero{};
  std::uint8_t homology_one{};
  std::uint8_t factor_count{};
  bool domain_characteristic_agrees{};
  bool factor_exact{};
  bool exact{};
};

struct causal_toric_map_section final {
  causal_integer_matrix character{};
  causal_matrix_analysis analysis{};
  std::int64_t smith[2]{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t free_cokernel_rank{};
  bool smith_exact{};
  bool exact{};
};

struct causal_toric_section final {
  causal_toric_map_section source[2]{};
  causal_toric_map_section blowup{};
  exact::word identity{};
  exact::word lineage{};
  std::int64_t exceptional_square{};
  std::uint8_t source_positive{};
  std::uint8_t source_negative{};
  std::uint8_t blowup_positive{};
  std::uint8_t blowup_negative{};
  bool topology_changed{};
  bool exact{};
};

struct causal_variation_section final {
  std::int64_t pencil[2][2][2]{};
  std::int64_t determinant[3]{};
  std::int64_t form[2][2]{};
  std::int64_t loops[3][2][2]{};
  causal_integer_matrix tensor{};
  causal_characteristic_receipt tensor_characteristic{};
  std::uint8_t ranks[3]{};
  std::int8_t parameters[3]{};
  exact::word identity{};
  exact::word lineage{};
  bool rank_strata_exact{};
  bool adjoints_exact{};
  bool exterior_exact{};
  bool exact{};
};

struct causal_control_section final {
  causal_characteristic_receipt identity_characteristic{};
  causal_characteristic_receipt jordan_characteristic{};
  exact::small_rational gaussian_vector[2][2]{};
  exact::word identity{};
  exact::word lineage{};
  std::int64_t rational_discriminant{};
  std::uint8_t identity_fixed{};
  std::uint8_t jordan_fixed{};
  bool equal_characteristic_unequal_fixed{};
  bool unequal_kernel_placement{};
  bool conjugacy_exact{};
  bool rational_eigenvalue_absent{};
  bool gaussian_eigenpair_exact{};
  bool exact{};
};

struct causal_linear_receipt final {
  causal_linear_card mounted{};
  causal_linear_question question{};
  causal_phase_section phase{};
  causal_cm_section cm{};
  causal_toric_section toric{};
  causal_variation_section variation{};
  causal_control_section controls{};
  causal_linear_plan theory{};
  causal_linear_obstruction obstruction{causal_linear_obstruction::invalid_foundation};
  std::uint8_t source_mask{};
  bool source_sections_independent{};
  bool alternatives_retained{};
  bool no_expected_invariants{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
