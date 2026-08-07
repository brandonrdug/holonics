#pragma once

#include <holonics/organ/cultivated_organ_receipt.hpp>
#include <holonics/organ/elementary_calculus_schema.hpp>

namespace holonics::organ {

enum class elementary_obstruction : std::uint8_t {
  none,
  collision,
  nonzero_boundary,
  incomplete_successor,
  unequal_successor,
  no_contact,
  no_obstruction,
  fiber_violation,
  path_residual,
  predicate_error,
  insufficient_rows,
  full_rank,
  nonunique_kernel,
  organ_absent,
  heldout_residual
};

struct identity_mask_receipt final {
  std::uint8_t mask{};
  std::uint8_t fields{};
  std::uint8_t collisions{};
  elementary_obstruction obstruction{elementary_obstruction::collision};
  bool selected{};
};

struct boundary_candidate_receipt final {
  std::int64_t residual[4][elementary_face_count]{};
  std::uint8_t candidate{};
  elementary_obstruction obstruction{elementary_obstruction::nonzero_boundary};
  bool diagonal_cancelled{};
  bool selected{};
};

struct occurrence_incidence_receipt final {
  identity_mask_receipt masks[31]{};
  boundary_candidate_receipt boundaries[4]{};
  std::uint8_t selected_mask{};
  bool payload_collapse_refuted{};
  bool boundary_squared_zero{};
  bool coherent_reorientation_exact{};
  bool theory_formed{};
};

enum class successor_signature_code : std::uint8_t {
  ordered,
  equal_complete,
  residual_complete,
  blocked,
  unresolved
};

struct composition_signature_receipt final {
  std::int64_t residual[4]{};
  successor_signature_code code{successor_signature_code::unresolved};
  std::uint8_t visible{};
  bool contact{};
  bool predecessor_link{};
  bool forward_complete{};
  bool reverse_complete{};
  bool complete_equal{};
  bool obstruction_present{};
};

struct composition_receipt final {
  composition_signature_receipt signatures[elementary_composition_count]{};
  bool pairwise_distinct{};
  bool scalar_only_refuted{};
  bool theory_formed{};
};

struct receiver_pair_receipt final {
  std::uint8_t left{};
  std::uint8_t right{};
  bool same_coarse{};
  bool same_fine{};
  bool same_first{};
  bool same_strict{};
};

struct receiver_receipt final {
  receiver_pair_receipt pairs[15]{};
  std::uint8_t pair_count{};
  std::uint8_t coarse_fibers{};
  std::uint8_t fine_fibers{};
  std::uint8_t coarse_strict_witnesses{};
  bool first_factors_coarse{};
  bool strict_factors_coarse{};
  bool strict_factors_fine{};
  bool refinement_exact{};
  bool unequal_sources_retained{};
  bool theory_formed{};
};

struct chart_receipt final {
  exact_matrix2 first_path{};
  exact_matrix2 second_path{};
  exact_matrix2 residual{};
  exact_matrix2 closed_word{};
  exact_matrix2 flat_word{};
  exact_matrix2 first_inverse{};
  exact_matrix2 second_inverse{};
  std::int64_t determinant{};
  std::int64_t trace{};
  bool curved{};
  bool flat_control{};
  bool theory_formed{};
};

struct conduct_candidate_receipt final {
  std::uint16_t code{};
  std::uint8_t conditions{};
  std::uint8_t errors{};
  bool selected{};
};

struct conduct_receipt final {
  conduct_candidate_receipt candidates[elementary_conduct_candidate_count]{};
  std::uint8_t selected_conditions[elementary_conduct_field_count]{};
  std::uint16_t selected_code{};
  std::uint8_t selected_population{};
  bool unique_least{};
  bool theory_formed{};
};

struct self_organ_receipt final {
  feature_geometry_receipt candidates[3]{};
  cultivated_shift_organ organ{};
  exact::small_rational trace[elementary_trace_count]{};
  std::uint8_t trace_count{};
  bool selected_exact{};
};

struct elementary_calculus_receipt final {
  occurrence_incidence_receipt occurrence{};
  composition_receipt composition{};
  receiver_receipt receiver{};
  chart_receipt chart{};
  conduct_receipt conduct{};
  self_organ_receipt self_organ{};
  exact::word passage{};
  exact::word lineage{};
  bool development_ports_distinct{};
  bool connected{};
  bool theory_formed{};
};

struct heldout_holonomy_receipt final {
  exact_matrix2 product{};
  tail_receipt tail{};
  cultivation_obstruction exclusion{cultivation_obstruction::none};
  cultivation_obstruction changed{cultivation_obstruction::none};
  exact::word passage{};
  exact::word lineage{};
  bool development_sources_absent{};
  bool prediction_before_comparison{};
  bool ablation_exact{};
  bool improved{};
  bool theory_formed{};
};

struct elementary_workspace final {
  exact::small_rational matrix[cultivation_row_capacity][cultivation_feature_capacity]{};
};

struct heldout_workspace final {
  exact::small_rational hidden[elementary_trace_count]{};
  exact::small_rational changed[elementary_trace_count]{};
};

}  // namespace holonics::organ
