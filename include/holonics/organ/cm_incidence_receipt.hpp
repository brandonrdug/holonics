#pragma once

#include <holonics/organ/cm_incidence_schema.hpp>

namespace holonics::organ {

struct cm_translation_receipt final {
  exact::word identity{};
  cm_element value{};
  cm_element conjugate{};
  cm_element norm{};
  std::uint64_t lineage{};
  std::uint8_t residue_mask{};
  bool norm_one{};
  bool exact{};
};

struct cm_edge_receipt final {
  exact::word identity{};
  std::uint64_t lineage{};
  std::uint8_t source{};
  std::uint8_t target{};
  std::uint8_t direction{};
  bool retained{};
};

struct cm_factor_receipt final {
  std::int64_t coefficients[cm_factor_capacity]{};
  std::uint8_t degree{};
  std::uint8_t multiplicity{};
  bool exact{};
};

struct cm_graph_receipt final {
  exact::word identity{};
  std::uint8_t adjacency[cm_point_capacity][cm_point_capacity]{};
  cm_edge_receipt edges[cm_edge_capacity]{};
  std::int64_t traces[cm_point_capacity]{};
  std::int64_t characteristic[cm_characteristic_capacity]{};
  cm_factor_receipt factors[cm_factor_capacity]{};
  std::int16_t character_eigenvalue[cm_point_capacity]{};
  std::uint8_t degree[cm_point_capacity]{};
  std::uint64_t lineage{};
  std::uint8_t edge_count{};
  std::uint8_t factor_count{};
  bool symmetric{};
  bool characteristic_exact{};
  bool exact{};
};

struct cm_projection_receipt final {
  exact::word identity{};
  cm_element points[cm_point_capacity]{};
  std::uint8_t expanded_adjacency[cm_point_capacity][cm_point_capacity]{};
  std::uint8_t direction_population[cm_translation_capacity]{};
  cm_edge_receipt lost[cm_edge_capacity]{};
  std::uint64_t lineage{};
  std::uint8_t unit_pair_count{};
  std::uint8_t lost_count{};
  std::uint8_t projection_loss{};
  std::uint8_t distinct_scalar_sums{};
  bool basis_injective{};
  bool factor_expansion_agree{};
  bool exact{};
};

struct cm_scattering_receipt final {
  exact::word identity{};
  std::uint8_t commutator_nonzero[cm_degree_capacity]{};
  std::uint8_t commutator_square[cm_degree_capacity]{};
  std::uint64_t lineage{};
  bool interchange_broken{};
  bool exact{};
};

struct cm_candidate_receipt final {
  cm_candidate_kind kind{};
  exact::word identity{};
  std::uint64_t lineage{};
  std::uint8_t expected{};
  std::uint8_t returned{};
  bool contact_exact{};
  bool injective{};
  bool admitted{};
};

struct cm_incidence_receipt final {
  cm_incidence_question question{};
  cm_problem_card mounted{};
  cm_translation_receipt translations[cm_translation_capacity]{};
  cm_graph_receipt periodic{};
  cm_graph_receipt window{};
  cm_projection_receipt projection{};
  cm_scattering_receipt scattering{};
  cm_candidate_receipt candidates[cm_candidate_capacity]{};
  cm_theory_plan theory{};
  cm_obstruction obstruction{cm_obstruction::invalid_foundation};
  std::uint8_t returned_translations{};
  bool no_expected_incidence{};
  bool no_expected_spectrum{};
  bool alternatives_retained{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ
